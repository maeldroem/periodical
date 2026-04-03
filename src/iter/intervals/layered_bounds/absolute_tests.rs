use std::error::Error;

use jiff::Zoned;

use super::absolute::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::iter::intervals::bounds::AbsoluteBoundsIteratorDispatcher;
use crate::iter::intervals::layered_bounds::abs_state_change::LayeredBoundsStateChangeAtAbsoluteBound;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn create() -> Result<(), Box<dyn Error>> {
    let first_layer_data = [
        AbsoluteStartBound::InfinitePast.to_bound(),
        AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsoluteEndBound::InfiniteFuture.to_bound(),
    ];

    let second_layer_data = [
        AbsoluteStartBound::InfinitePast.to_bound(),
        AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .to_bound(),
        AbsoluteEndBound::InfiniteFuture.to_bound(),
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
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 9
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 11
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new("2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 13
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    let second_layer_data = [
        // 2
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 8
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 10
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 12
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
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
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // B
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // C
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // D
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // E
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // F
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // G
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // H
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // I
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // J
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBound::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // K
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // L
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // M
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsoluteFiniteBound::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // N
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-02-26 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // O
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsoluteFiniteBound::new("2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // P
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-03-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // Q
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // R
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsoluteFiniteBound::new("2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // S
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsoluteFiniteBound::new("2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // T1
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
            ),
            // T2
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(
                    AbsoluteFiniteBound::new("2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-03-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound()
                ),
            ),
            // U
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBound::new("2025-03-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
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

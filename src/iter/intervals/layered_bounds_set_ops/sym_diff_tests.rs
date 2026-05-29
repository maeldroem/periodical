use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::sym_diff::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition, RelativeStartBound};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState,
    LayeredBoundsStateChangeAtAbsoluteBound,
    LayeredBoundsStateChangeAtRelativeBound,
};

mod abs {
    use super::*;

    #[test]
    fn create() -> Result<(), Box<dyn Error>> {
        let data = [
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                None,
                Some(AbsoluteStartBound::InfinitePast),
            ),
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ),
                Some(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                ),
            ),
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                Some(
                    AbsoluteFiniteBoundPosition::new("2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                ),
            ),
        ];

        let _ = LayeredAbsoluteBoundsSymmetricDifference::new(data.into_iter());

        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    #[test]
    fn run() -> Result<(), Box<dyn Error>> {
        // first layer:    [---2---]  [5]  [-6-]   [--9--]
        // second layer: [-1-] [3] (--4--) (-7-) [--8--]
        let first_layer_data = [
            // 2
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 5
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-28 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 6
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 9
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        let second_layer_data = [
            // 1
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 3
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 4
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 7
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 8
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        // first layer:    [---2---]  [5]  [-6-]   [--9--]
        // second layer: [-1-] [3] (--4--) (-7-) [--8--]
        // ref:          AA   B   CCCC   D E   F GG     HH
        assert_eq!(
            first_layer_data
                .abs_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.abs_bounds_iter().unite_bounds())
                .abs_symmetric_difference_layered()
                .collect::<Vec<_>>(),
            vec![
                // A
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // B
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // C
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // D
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-28 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // E
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ),
                // F
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ),
                // G
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // H
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ),
            ],
        );

        Ok(())
    }
}

mod rel {
    use super::*;

    #[test]
    fn create() {
        let data = [
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                None,
                Some(RelativeStartBound::InfinitePast),
            ),
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(101)).to_end_bound()),
                Some(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(101),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                ),
            ),
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(501),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(501)).to_start_bound()),
            ),
        ];

        let _ = LayeredRelativeBoundsSymmetricDifference::new(data.into_iter());
    }

    #[allow(clippy::too_many_lines)]
    #[test]
    fn run() {
        // first layer:    [---2---]  [5]  [-6-]   [--9--]
        // second layer: [-1-] [3] (--4--) (-7-) [--8--]
        let first_layer_data = [
            // 2
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(105)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(120)).to_end_bound(),
            ),
            // 5
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(125)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(128)).to_end_bound(),
            ),
            // 6
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(201)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(205)).to_end_bound(),
            ),
            // 9
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(215)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(225)).to_end_bound(),
            ),
        ];

        let second_layer_data = [
            // 1
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(101)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(110)).to_end_bound(),
            ),
            // 3
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(112)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(115)).to_end_bound(),
            ),
            // 4
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(120), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(130), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            ),
            // 7
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(201), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(205), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            ),
            // 8
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(210)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(220)).to_end_bound(),
            ),
        ];

        // first layer:    [---2---]  [5]  [-6-]   [--9--]
        // second layer: [-1-] [3] (--4--) (-7-) [--8--]
        // ref:          AA   B   CCCC   D E   F GG     HH
        assert_eq!(
            first_layer_data
                .rel_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.rel_bounds_iter().unite_bounds())
                .rel_symmetric_difference_layered()
                .collect::<Vec<_>>(),
            vec![
                // A
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(101)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(105),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // B
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(110),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(112),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // C
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(115),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(125),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // D
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(128),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(130),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // E
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(201)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(201)).to_end_bound(),
                ),
                // F
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(205)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(205)).to_end_bound(),
                ),
                // G
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(210)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(215),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                // H
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(220),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(225)).to_end_bound(),
                ),
            ],
        );
    }
}

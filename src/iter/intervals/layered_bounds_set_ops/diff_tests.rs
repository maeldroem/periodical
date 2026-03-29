use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::diff::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
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
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ))),
            ),
        ];

        let _ = LayeredAbsoluteBoundsDifference::new(data.into_iter());

        Ok(())
    }

    #[test]
    fn run() -> Result<(), Box<dyn Error>> {
        // first layer:     [------2------]     [--6--] [8]
        // second layer: [-1-] (-3-)  [-4-) [-5-]     [--7--]
        let first_layer_data = [
            // 2
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 6
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 8
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
        ];

        let second_layer_data = [
            // 1
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-07 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 3
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 4
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 5
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
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
        ];

        assert_eq!(
            first_layer_data
                .abs_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.abs_bounds_iter().unite_bounds())
                .abs_difference_layered()
                .collect::<Vec<_>>(),
            vec![
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-07 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                    )),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                    )),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
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
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(101),
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(501),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(501),
                ))),
            ),
        ];

        let _ = LayeredRelativeBoundsDifference::new(data.into_iter());
    }

    #[test]
    fn run() {
        // first layer:     [------2------]     [--6--] [8]
        // second layer: [-1-] (-3-)  [-4-) [-5-]     [--7--]
        let first_layer_data = [
            // 2
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(125))),
            ),
            // 6
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(205))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(215))),
            ),
            // 8
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(217))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(223))),
            ),
        ];

        let second_layer_data = [
            // 1
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(107))),
            ),
            // 3
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(110),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(115),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 4
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(120))),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(125),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 5
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(201))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(205))),
            ),
            // 7
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(215))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(225))),
            ),
        ];

        assert_eq!(
            first_layer_data
                .rel_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.rel_bounds_iter().unite_bounds())
                .rel_difference_layered()
                .collect::<Vec<_>>(),
            vec![
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(107),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(110))),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(115))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(120),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(125))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(125))),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(205),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(215),
                        BoundInclusivity::Exclusive,
                    )),
                ),
            ],
        );
    }
}

use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::intersect::*;
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
                Some(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                ),
            ),
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
                Some(
                    AbsoluteFiniteBound::new("2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                ),
            ),
        ];

        let _ = LayeredAbsoluteBoundsIntersection::new(data.into_iter());

        Ok(())
    }

    #[test]
    fn run() -> Result<(), Box<dyn Error>> {
        // first layer:  [--1--]       [-3-] [-----5-----)
        // second layer:       [--2--]       [--4--]  (--6--]
        let first_layer_data = [
            // 1
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 3
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 5
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ];

        let second_layer_data = [
            // 2
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 4
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-22 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            // 6
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
        ];

        assert_eq!(
            first_layer_data
                .abs_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.abs_bounds_iter().unite_bounds())
                .abs_intersect_layered()
                .collect::<Vec<_>>(),
            vec![
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                        "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                    )),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                        "2025-01-22 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                    )),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
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

        let _ = LayeredRelativeBoundsIntersection::new(data.into_iter());
    }

    #[test]
    fn run() {
        // first layer:  [--1--]       [-3-] [-----5-----)
        // second layer:       [--2--]       [--4--]  (--6--]
        let first_layer_data = [
            // 1
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
            ),
            // 3
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(111))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(115))),
            ),
            // 5
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(120))),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(210),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ];

        let second_layer_data = [
            // 2
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(110))),
            ),
            // 4
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(120))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(122))),
            ),
            // 6
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(201),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(215))),
            ),
        ];

        assert_eq!(
            first_layer_data
                .rel_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.rel_bounds_iter().unite_bounds())
                .rel_intersect_layered()
                .collect::<Vec<_>>(),
            vec![
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(120))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(122))),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(201),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(210),
                        BoundInclusivity::Exclusive,
                    )),
                ),
            ],
        );
    }
}

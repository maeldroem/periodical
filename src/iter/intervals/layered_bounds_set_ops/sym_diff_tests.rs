use std::error::Error;

use jiff::{SignedDuration, Zoned};

use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};

use super::sym_diff::*;

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
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()))),
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
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()))),
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
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            ),
            // 5
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-28 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            ),
            // 6
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            ),
            // 9
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            ),
        ];
    
        let second_layer_data = [
            // 1
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            ),
            // 3
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            ),
            // 4
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 7
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 8
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
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
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // B
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // C
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // D
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-28 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // E
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                ),
                // F
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                ),
                // G
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // H
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-02-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-02-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
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
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101)))),
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
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(
                    501,
                )))),
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
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(105))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(120))),
            ),
            // 5
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(125))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(128))),
            ),
            // 6
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(201))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(205))),
            ),
            // 9
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(215))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(225))),
            ),
        ];
    
        let second_layer_data = [
            // 1
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(110))),
            ),
            // 3
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(112))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(115))),
            ),
            // 4
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(120),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(130),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 7
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(201),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(205),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 8
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(210))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(220))),
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
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(105),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // B
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(110),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(112),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // C
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(115),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(125),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // D
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(128),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(130),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // E
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(201))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(201))),
                ),
                // F
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(205))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(205))),
                ),
                // G
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(210))),
                    RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(215),
                        BoundInclusivity::Exclusive,
                    )),
                ),
                // H
                RelativeBoundPair::new(
                    RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(220),
                        BoundInclusivity::Exclusive,
                    )),
                    RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(225))),
                ),
            ],
        );
    }
}

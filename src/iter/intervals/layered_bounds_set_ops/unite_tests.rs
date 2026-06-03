use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::unite::*;
use crate::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelBoundPair, RelFiniteBoundPos, RelStartBound};
use crate::iter::intervals::bounds::{AbsBoundsIteratorDispatcher, RelBoundsIteratorDispatcher};
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState,
    LayeredBoundsStateChangeAtAbsBound,
    LayeredBoundsStateChangeAtRelBound,
};

mod abs {
    use super::*;

    #[test]
    fn create() -> Result<(), Box<dyn Error>> {
        let data = [
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                None,
                Some(AbsStartBound::InfinitePast),
            ),
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(
                    AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ),
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                ),
            ),
            LayeredBoundsStateChangeAtAbsBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                Some(
                    AbsFiniteBoundPos::new("2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                ),
            ),
        ];

        let _ = LayeredAbsBoundsUnion::new(data.into_iter());

        Ok(())
    }

    #[test]
    fn run() -> Result<(), Box<dyn Error>> {
        // first layer:    [--1--] [3] [--4--)     [-6-]
        // second layer:     (----2----)     (-5-]
        let first_layer_data = [
            // 1
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 3
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 4
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 6
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        let second_layer_data = [
            // 2
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 5
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        assert_eq!(
            first_layer_data
                .abs_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.abs_bounds_iter().unite_bounds())
                .abs_unite_layered()
                .collect::<Vec<_>>(),
            vec![
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
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
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                None,
                Some(RelStartBound::InfinitePast),
            ),
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
                Some(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(101),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                ),
            ),
            LayeredBoundsStateChangeAtRelBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(501),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                Some(RelFiniteBoundPos::new(SignedDuration::from_hours(501)).to_start_bound()),
            ),
        ];

        let _ = LayeredRelBoundsUnion::new(data.into_iter());
    }

    #[test]
    fn run() {
        // first layer:    [--1--] [3] [--4--)     [-6-]
        // second layer:     (----2----)     (-5-]
        let first_layer_data = [
            // 1
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(110)).to_end_bound(),
            ),
            // 3
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(112)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(115)).to_end_bound(),
            ),
            // 4
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(120)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(125),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 6
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(201)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(205)).to_end_bound(),
            ),
        ];

        let second_layer_data = [
            // 2
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(105),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(120),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 5
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(125),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(130)).to_end_bound(),
            ),
        ];

        assert_eq!(
            first_layer_data
                .rel_bounds_iter()
                .unite_bounds()
                .layer(second_layer_data.rel_bounds_iter().unite_bounds())
                .rel_unite_layered()
                .collect::<Vec<_>>(),
            vec![
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(125),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(125),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(130)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(201)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(205)).to_end_bound(),
                ),
            ],
        );
    }
}

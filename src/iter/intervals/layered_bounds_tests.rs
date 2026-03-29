use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::layered_bounds::*;
use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelativeBound,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};

mod layered_bounds_state {
    use super::*;

    #[test]
    fn is_first_layer_active() {
        assert!(!LayeredBoundsState::NoLayers.is_first_layer_active());
        assert!(LayeredBoundsState::FirstLayer.is_first_layer_active());
        assert!(!LayeredBoundsState::SecondLayer.is_first_layer_active());
        assert!(LayeredBoundsState::BothLayers.is_first_layer_active());
    }

    #[test]
    fn is_second_layer_active() {
        assert!(!LayeredBoundsState::NoLayers.is_second_layer_active());
        assert!(!LayeredBoundsState::FirstLayer.is_second_layer_active());
        assert!(LayeredBoundsState::SecondLayer.is_second_layer_active());
        assert!(LayeredBoundsState::BothLayers.is_second_layer_active());
    }

    #[test]
    fn add_no_layers_no_layers() {
        assert_eq!(
            LayeredBoundsState::NoLayers + LayeredBoundsState::NoLayers,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn add_no_layers_first_layer() {
        assert_eq!(
            LayeredBoundsState::NoLayers + LayeredBoundsState::FirstLayer,
            LayeredBoundsState::FirstLayer
        );
    }

    #[test]
    fn add_no_layers_second_layer() {
        assert_eq!(
            LayeredBoundsState::NoLayers + LayeredBoundsState::SecondLayer,
            LayeredBoundsState::SecondLayer
        );
    }

    #[test]
    fn add_no_layers_both_layers() {
        assert_eq!(
            LayeredBoundsState::NoLayers + LayeredBoundsState::BothLayers,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_first_layer_no_layers() {
        assert_eq!(
            LayeredBoundsState::FirstLayer + LayeredBoundsState::NoLayers,
            LayeredBoundsState::FirstLayer
        );
    }

    #[test]
    fn add_first_layer_first_layer() {
        assert_eq!(
            LayeredBoundsState::FirstLayer + LayeredBoundsState::FirstLayer,
            LayeredBoundsState::FirstLayer
        );
    }

    #[test]
    fn add_first_layer_second_layer() {
        assert_eq!(
            LayeredBoundsState::FirstLayer + LayeredBoundsState::SecondLayer,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_first_layer_both_layers() {
        assert_eq!(
            LayeredBoundsState::FirstLayer + LayeredBoundsState::BothLayers,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_second_layer_no_layers() {
        assert_eq!(
            LayeredBoundsState::SecondLayer + LayeredBoundsState::NoLayers,
            LayeredBoundsState::SecondLayer
        );
    }

    #[test]
    fn add_second_layer_first_layer() {
        assert_eq!(
            LayeredBoundsState::SecondLayer + LayeredBoundsState::FirstLayer,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_second_layer_second_layer() {
        assert_eq!(
            LayeredBoundsState::SecondLayer + LayeredBoundsState::SecondLayer,
            LayeredBoundsState::SecondLayer
        );
    }

    #[test]
    fn add_second_layer_both_layers() {
        assert_eq!(
            LayeredBoundsState::SecondLayer + LayeredBoundsState::BothLayers,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_both_layers_no_layers() {
        assert_eq!(
            LayeredBoundsState::BothLayers + LayeredBoundsState::NoLayers,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_both_layers_first_layer() {
        assert_eq!(
            LayeredBoundsState::BothLayers + LayeredBoundsState::FirstLayer,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_both_layers_second_layer() {
        assert_eq!(
            LayeredBoundsState::BothLayers + LayeredBoundsState::SecondLayer,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn add_both_layers_both_layers() {
        assert_eq!(
            LayeredBoundsState::BothLayers + LayeredBoundsState::BothLayers,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn sub_no_layers_no_layers() {
        assert_eq!(
            LayeredBoundsState::NoLayers - LayeredBoundsState::NoLayers,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_no_layers_first_layer() {
        assert_eq!(
            LayeredBoundsState::NoLayers - LayeredBoundsState::FirstLayer,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_no_layers_second_layer() {
        assert_eq!(
            LayeredBoundsState::NoLayers - LayeredBoundsState::SecondLayer,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_no_layers_both_layers() {
        assert_eq!(
            LayeredBoundsState::NoLayers - LayeredBoundsState::BothLayers,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_first_layer_no_layers() {
        assert_eq!(
            LayeredBoundsState::FirstLayer - LayeredBoundsState::NoLayers,
            LayeredBoundsState::FirstLayer
        );
    }

    #[test]
    fn sub_first_layer_first_layer() {
        assert_eq!(
            LayeredBoundsState::FirstLayer - LayeredBoundsState::FirstLayer,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_first_layer_second_layer() {
        assert_eq!(
            LayeredBoundsState::FirstLayer - LayeredBoundsState::SecondLayer,
            LayeredBoundsState::FirstLayer
        );
    }

    #[test]
    fn sub_first_layer_both_layers() {
        assert_eq!(
            LayeredBoundsState::FirstLayer - LayeredBoundsState::BothLayers,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_second_layer_no_layers() {
        assert_eq!(
            LayeredBoundsState::SecondLayer - LayeredBoundsState::NoLayers,
            LayeredBoundsState::SecondLayer
        );
    }

    #[test]
    fn sub_second_layer_first_layer() {
        assert_eq!(
            LayeredBoundsState::SecondLayer - LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer
        );
    }

    #[test]
    fn sub_second_layer_second_layer() {
        assert_eq!(
            LayeredBoundsState::SecondLayer - LayeredBoundsState::SecondLayer,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_second_layer_both_layers() {
        assert_eq!(
            LayeredBoundsState::SecondLayer - LayeredBoundsState::BothLayers,
            LayeredBoundsState::NoLayers
        );
    }

    #[test]
    fn sub_both_layers_no_layers() {
        assert_eq!(
            LayeredBoundsState::BothLayers - LayeredBoundsState::NoLayers,
            LayeredBoundsState::BothLayers
        );
    }

    #[test]
    fn sub_both_layers_first_layer() {
        assert_eq!(
            LayeredBoundsState::BothLayers - LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer
        );
    }

    #[test]
    fn sub_both_layers_second_layer() {
        assert_eq!(
            LayeredBoundsState::BothLayers - LayeredBoundsState::SecondLayer,
            LayeredBoundsState::FirstLayer
        );
    }

    #[test]
    fn sub_both_layers_both_layers() {
        assert_eq!(
            LayeredBoundsState::BothLayers - LayeredBoundsState::BothLayers,
            LayeredBoundsState::NoLayers
        );
    }
}

mod layered_bounds_state_change {
    use super::*;

    #[test]
    fn at_abs_bound_old_state() {
        assert_eq!(
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                None,
                None,
            )
            .old_state(),
            LayeredBoundsState::FirstLayer,
        );
    }

    #[test]
    fn at_abs_bound_new_state() {
        assert_eq!(
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                None,
                None,
            )
            .new_state(),
            LayeredBoundsState::SecondLayer,
        );
    }

    #[test]
    fn at_abs_bound_old_state_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            )
            .old_state_end(),
            Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            ))),
        );

        Ok(())
    }

    #[test]
    fn at_abs_bound_new_state_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ))),
            )
            .new_state_start(),
            Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            ))),
        );

        Ok(())
    }

    #[test]
    fn at_rel_bound_old_state() {
        assert_eq!(
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                None,
                None,
            )
            .old_state(),
            LayeredBoundsState::FirstLayer,
        );
    }

    #[test]
    fn at_rel_bound_new_state() {
        assert_eq!(
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                None,
                None,
            )
            .new_state(),
            LayeredBoundsState::SecondLayer,
        );
    }

    #[test]
    fn at_rel_bound_old_state_end() {
        assert_eq!(
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Inclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ))),
            )
            .old_state_end(),
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ))),
        );
    }

    #[test]
    fn at_rel_bound_new_state_start() {
        assert_eq!(
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Inclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ))),
            )
            .new_state_start(),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ))),
        );
    }
}

mod layered_abs_bounds {
    use super::*;

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
}

mod layered_rel_bounds {
    use super::*;

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
}

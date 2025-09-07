use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};
use crate::test_utils::date;

use super::diff::*;

#[test]
fn create_layered_abs_bounds_diff() {
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
            Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 1,
            )))),
            Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))),
        ),
        LayeredBoundsStateChangeAtAbsoluteBound::new(
            LayeredBoundsState::SecondLayer,
            LayeredBoundsState::NoLayers,
            Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 5, 1),
                BoundInclusivity::Exclusive,
            ))),
            Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 5, 1,
            )))),
        ),
    ];

    let _ = LayeredAbsoluteBoundsDifference::new(data.into_iter());
}

#[test]
fn layered_abs_bounds_diff_run() {
    // first layer:     [------2------]     [--6--] [8]
    // second layer: [-1-] (-3-)  [-4-) [-5-]     [--7--]
    let first_layer_data = [
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 15))),
        ),
        // 8
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 17))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 23))),
        ),
    ];

    let second_layer_data = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 7))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 10),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 15),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 25),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 25))),
        ),
    ];

    assert_eq!(
        first_layer_data
            .abs_bounds_iter()
            .united()
            .layer(second_layer_data.abs_bounds_iter().united())
            .difference()
            .collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 7),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 20),
                    BoundInclusivity::Exclusive,
                )),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 5),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 15),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );
}

#[test]
fn create_layered_rel_bounds_diff() {
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
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(101)))),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(101),
                BoundInclusivity::Exclusive,
            ))),
        ),
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::SecondLayer,
            LayeredBoundsState::NoLayers,
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(501),
                BoundInclusivity::Exclusive,
            ))),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                501,
            )))),
        ),
    ];

    let _ = LayeredRelativeBoundsDifference::new(data.into_iter());
}

#[test]
fn layered_rel_bounds_diff_run() {
    // first layer:     [------2------]     [--6--] [8]
    // second layer: [-1-] (-3-)  [-4-) [-5-]     [--7--]
    let first_layer_data = [
        // 2
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(125))),
        ),
        // 6
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(215))),
        ),
        // 8
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(217))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(223))),
        ),
    ];

    let second_layer_data = [
        // 1
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(107))),
        ),
        // 3
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(110),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(115),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 4
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(125),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
        ),
        // 7
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(215))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(225))),
        ),
    ];

    assert_eq!(
        first_layer_data
            .rel_bounds_iter()
            .united()
            .layer(second_layer_data.rel_bounds_iter().united())
            .difference()
            .collect::<Vec<_>>(),
        vec![
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(107),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(110))),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(115))),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(120),
                    BoundInclusivity::Exclusive,
                )),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(125))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(125))),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(205),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(215),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );
}

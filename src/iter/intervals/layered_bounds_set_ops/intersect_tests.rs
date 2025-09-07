use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::iter::intervals::bounds::{AbsoluteBoundsIterDispatcher, RelativeBoundsIterDispatcher};
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};
use crate::test_utils::date;

use super::intersect::*;

#[test]
fn create_layered_abs_bounds_intersection() {
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

    let _ = LayeredAbsoluteBoundsIntersection::new(data.into_iter());
}

#[test]
fn create_layered_abs_bounds_intersection_run() {
    // first layer:  [--1--]       [-3-] [-----5-----)
    // second layer:       [--2--]       [--4--]  (--6--]
    let first_layer_data = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 11))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 10),
                BoundInclusivity::Exclusive,
            )),
        ),
    ];

    let second_layer_data = [
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 22))),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 15))),
        ),
    ];

    assert_eq!(
        first_layer_data
            .abs_bounds_iter()
            .united()
            .layer(second_layer_data.abs_bounds_iter().united())
            .intersect()
            .collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 22))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 1),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 10),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );
}

#[test]
fn create_layered_rel_bounds_intersection() {
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

    let _ = LayeredRelativeBoundsIntersection::new(data.into_iter());
}

#[test]
fn create_layered_rel_bounds_intersection_run() {
    // first layer:  [--1--]       [-3-] [-----5-----)
    // second layer:       [--2--]       [--4--]  (--6--]
    let first_layer_data = [
        // 1
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
        ),
        // 3
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(111))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(115))),
        ),
        // 5
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(210),
                BoundInclusivity::Exclusive,
            )),
        ),
    ];

    let second_layer_data = [
        // 2
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(110))),
        ),
        // 4
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(122))),
        ),
        // 6
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(201),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(215))),
        ),
    ];

    assert_eq!(
        first_layer_data
            .rel_bounds_iter()
            .united()
            .layer(second_layer_data.rel_bounds_iter().united())
            .intersect()
            .collect::<Vec<_>>(),
        vec![
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(122))),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(201),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(210),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );
}

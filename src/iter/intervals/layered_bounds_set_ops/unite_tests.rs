use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};
use crate::iter::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};
use crate::test_utils::date;

use super::unite::*;

#[test]
fn create_layered_abs_bounds_union() {
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

    let _ = LayeredAbsoluteBoundsUnion::new(data.into_iter());
}

#[test]
fn layered_abs_bounds_union_run() {
    // first layer:    [--1--] [3] [--4--)     [-6-]
    // second layer:     (----2----)     (-5-]
    let first_layer_data = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 25),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
    ];

    let second_layer_data = [
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 25),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
        ),
    ];

    assert_eq!(
        first_layer_data
            .abs_bounds_iter()
            .united()
            .layer(second_layer_data.abs_bounds_iter().united())
            .unite()
            .collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 25),
                    BoundInclusivity::Exclusive,
                )),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 25),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            ),
        ],
    );
}

#[test]
fn create_layered_rel_bounds_union() {
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

    let _ = LayeredRelativeBoundsUnion::new(data.into_iter());
}

#[test]
fn layered_rel_bounds_union_run() {
    // first layer:    [--1--] [3] [--4--)     [-6-]
    // second layer:     (----2----)     (-5-]
    let first_layer_data = [
        // 1
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(110))),
        ),
        // 3
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(112))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(115))),
        ),
        // 4
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(125),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
        ),
    ];

    let second_layer_data = [
        // 2
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(105),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(120),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(125),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(130))),
        ),
    ];

    assert_eq!(
        first_layer_data
            .rel_bounds_iter()
            .united()
            .layer(second_layer_data.rel_bounds_iter().united())
            .unite()
            .collect::<Vec<_>>(),
        vec![
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(125),
                    BoundInclusivity::Exclusive,
                )),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(125),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(130))),
            ),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
            ),
        ],
    );
}

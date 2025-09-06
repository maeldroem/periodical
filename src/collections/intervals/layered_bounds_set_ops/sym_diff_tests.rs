use chrono::{Duration, Utc};

use crate::collections::intervals::bounds::{AbsoluteBoundsIterDispatcher, RelativeBoundsIterDispatcher};
use crate::collections::intervals::layered_bounds::{
    LayeredBoundsState, LayeredBoundsStateChangeAtAbsoluteBound, LayeredBoundsStateChangeAtRelativeBound,
};
use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::test_utils::date;

use super::sym_diff::*;

#[test]
fn create_layered_abs_bounds_sym_diff() {
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

    let _ = LayeredAbsoluteBoundsSymmetricDifference::new(data.into_iter());
}

#[allow(clippy::too_many_lines)]
#[test]
fn layered_abs_bounds_sym_diff_run() {
    // first layer:    [---2---]  [5]  [-6-]   [--9--]
    // second layer: [-1-] [3] (--4--) (-7-) [--8--]
    let first_layer_data = [
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 28))),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        // 9
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 25))),
        ),
    ];

    let second_layer_data = [
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
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 1),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 5),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 8
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 20))),
        ),
    ];

    // first layer:    [---2---]  [5]  [-6-]   [--9--]
    // second layer: [-1-] [3] (--4--) (-7-) [--8--]
    // ref:          AA   B   CCCC   D E   F GG     HH
    assert_eq!(
        first_layer_data
            .abs_bounds_iter()
            .united()
            .layer(second_layer_data.abs_bounds_iter().united())
            .symmetric_difference()
            .collect::<Vec<_>>(),
        vec![
            // A
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // B
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 10),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 12),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // C
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 15),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 25),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // D
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 28),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // E
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            ),
            // F
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            ),
            // G
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 15),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // H
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 20),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 25))),
            ),
        ],
    );
}

#[test]
fn create_layered_rel_bounds_sym_diff() {
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

    let _ = LayeredRelativeBoundsSymmetricDifference::new(data.into_iter());
}

#[allow(clippy::too_many_lines)]
#[test]
fn layered_rel_bounds_sym_diff_run() {
    // first layer:    [---2---]  [5]  [-6-]   [--9--]
    // second layer: [-1-] [3] (--4--) (-7-) [--8--]
    let first_layer_data = [
        // 2
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
        ),
        // 5
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(125))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(128))),
        ),
        // 6
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
        ),
        // 9
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(215))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(225))),
        ),
    ];

    let second_layer_data = [
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
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(120),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(130),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 7
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(201),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(205),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 8
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(210))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(220))),
        ),
    ];

    // first layer:    [---2---]  [5]  [-6-]   [--9--]
    // second layer: [-1-] [3] (--4--) (-7-) [--8--]
    // ref:          AA   B   CCCC   D E   F GG     HH
    assert_eq!(
        first_layer_data
            .rel_bounds_iter()
            .united()
            .layer(second_layer_data.rel_bounds_iter().united())
            .symmetric_difference()
            .collect::<Vec<_>>(),
        vec![
            // A
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(105),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // B
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(110),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(112),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // C
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(115),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(125),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // D
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(128),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(130),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // E
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
            ),
            // F
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
            ),
            // G
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(210))),
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(215),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // H
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(220),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(225))),
            ),
        ],
    );
}

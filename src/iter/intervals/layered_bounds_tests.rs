use chrono::{Duration, Utc};

use crate::intervals::absolute::{
    AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelativeBound, RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
};
use crate::iter::intervals::bounds::{AbsoluteBoundsIterDispatcher, RelativeBoundsIterDispatcher};
use crate::test_utils::date;

use super::layered_bounds::*;

#[test]
fn layered_bounds_state_is_first_layer_active() {
    assert!(!LayeredBoundsState::NoLayers.is_first_layer_active());
    assert!(LayeredBoundsState::FirstLayer.is_first_layer_active());
    assert!(!LayeredBoundsState::SecondLayer.is_first_layer_active());
    assert!(LayeredBoundsState::BothLayers.is_first_layer_active());
}

#[test]
fn layered_bounds_state_is_second_layer_active() {
    assert!(!LayeredBoundsState::NoLayers.is_second_layer_active());
    assert!(!LayeredBoundsState::FirstLayer.is_second_layer_active());
    assert!(LayeredBoundsState::SecondLayer.is_second_layer_active());
    assert!(LayeredBoundsState::BothLayers.is_second_layer_active());
}

#[test]
fn layered_bounds_state_add_no_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::NoLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_add_no_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn layered_bounds_state_add_no_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn layered_bounds_state_add_no_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_first_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::NoLayers,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn layered_bounds_state_add_first_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn layered_bounds_state_add_first_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_first_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_second_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::NoLayers,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn layered_bounds_state_add_second_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_second_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn layered_bounds_state_add_second_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_both_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::NoLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_both_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_both_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_add_both_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_sub_no_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::NoLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_no_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_no_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_no_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_first_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::NoLayers,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn layered_bounds_state_sub_first_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_first_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn layered_bounds_state_sub_first_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_second_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::NoLayers,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn layered_bounds_state_sub_second_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn layered_bounds_state_sub_second_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_second_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_sub_both_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::NoLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn layered_bounds_state_sub_both_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn layered_bounds_state_sub_both_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn layered_bounds_state_sub_both_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn layered_bounds_state_change_at_abs_bound_old_state() {
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
fn layered_bounds_state_change_at_abs_bound_new_state() {
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
fn layered_bounds_state_change_at_abs_bound_old_state_end() {
    assert_eq!(
        LayeredBoundsStateChangeAtAbsoluteBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            ))),
            Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))),
        )
        .old_state_end(),
        Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn layered_bounds_state_change_at_abs_bound_new_state_start() {
    assert_eq!(
        LayeredBoundsStateChangeAtAbsoluteBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
            ))),
            Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Exclusive,
            ))),
        )
        .new_state_start(),
        Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn layered_bounds_state_change_at_rel_bound_old_state() {
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
fn layered_bounds_state_change_at_rel_bound_new_state() {
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
fn layered_bounds_state_change_at_rel_bound_old_state_end() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Inclusive,
            ))),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            ))),
        )
        .old_state_end(),
        Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn layered_bounds_state_change_at_rel_bound_new_state_start() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Inclusive,
            ))),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(1),
                BoundInclusivity::Exclusive,
            ))),
        )
        .new_state_start(),
        Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(1),
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn layered_abs_bounds_create() {
    let first_layer_data = [
        AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 2,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 5,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
    ];

    let second_layer_data = [
        AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 2,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 5,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
    ];

    let _ = LayeredAbsoluteBounds::new(first_layer_data.into_iter(), second_layer_data.into_iter());
}

#[allow(clippy::too_many_lines)]
#[test]
fn layered_abs_bounds_run() {
    // first layer:  [--1--]            [--3--]             (--6--]  [--7--] [--9--)(--11-] [-13-]
    // second layer:           [--2--]        (--4--] [--5--]           [--8--] [10)(--12---]
    let first_layer_data = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 17))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 5),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 25))),
        ),
        // 9
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 26))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 3, 10),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 11
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 3, 10),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 15))),
        ),
        // 13
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 25))),
        ),
    ];

    let second_layer_data = [
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        // 8
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 1))),
        ),
        // 10
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 4))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 3, 10),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 12
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 3, 10),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 20))),
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
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 1
                )))),
            ),
            // B
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 5
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // C
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 10),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 10
                )))),
            ),
            // D
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 15
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 15),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // E
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 17),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 17
                )))),
            ),
            // F
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 20
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 20),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // G
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 25
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 25),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // H
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 1, 30
                )))),
            ),
            // I
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 2, 5
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 5),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // J
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 2, 10
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 10),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // K
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 15),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 2, 15
                )))),
            ),
            // L
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 20),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 2, 20
                )))),
            ),
            // M
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 2, 25
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 25),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // N
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 26),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 2, 26
                )))),
            ),
            // O
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 1
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 1),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // P
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 4),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 4
                )))),
            ),
            // Q
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 10),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 10
                )))),
            ),
            // R
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 10
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 10),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // S
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 15
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 15),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // T1
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 20),
                    BoundInclusivity::Exclusive,
                ))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 20
                )))),
            ),
            // T2
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 20
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 20),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // U
            LayeredBoundsStateChangeAtAbsoluteBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                    &Utc, 2025, 3, 25
                )))),
                Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 3, 25),
                    BoundInclusivity::Exclusive,
                ))),
            ),
        ],
    );
}

#[test]
fn layered_rel_bounds_create() {
    let first_layer_data = [
        RelativeBound::Start(RelativeStartBound::InfinitePast),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(102)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            105,
        )))),
        RelativeBound::End(RelativeEndBound::InfiniteFuture),
    ];

    let second_layer_data = [
        RelativeBound::Start(RelativeStartBound::InfinitePast),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(102)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            105,
        )))),
        RelativeBound::End(RelativeEndBound::InfiniteFuture),
    ];

    let _ = LayeredRelativeBounds::new(first_layer_data.into_iter(), second_layer_data.into_iter());
}

#[allow(clippy::too_many_lines)]
#[test]
fn layered_rel_bounds_run() {
    // first layer:  [--1--]            [--3--]             (--6--]  [--7--] [--9--)(--11-] [-13-]
    // second layer:           [--2--]        (--4--] [--5--]           [--8--] [10)(--12---]
    let first_layer_data = [
        // 1
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(105))),
        ),
        // 3
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(117))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(120))),
        ),
        // 6
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(205),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(210))),
        ),
        // 7
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(215))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(225))),
        ),
        // 9
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(226))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(310),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 11
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(310),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(315))),
        ),
        // 13
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(320))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(325))),
        ),
    ];

    let second_layer_data = [
        // 2
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(110))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(115))),
        ),
        // 4
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(120),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(125))),
        ),
        // 5
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(130))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205))),
        ),
        // 8
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(220))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(301))),
        ),
        // 10
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(304))),
            RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(310),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 12
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(310),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(320))),
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
                    Duration::hours(101),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    101
                )))),
            ),
            // B
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(105)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(105),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // C
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(110),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    110
                )))),
            ),
            // D
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(115)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(115),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // E
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(117),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    117
                )))),
            ),
            // F
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(120)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(120),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // G
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(125)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(125),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // H
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(130),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    130
                )))),
            ),
            // I
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(205)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(205),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // J
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(210)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(210),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // K
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(215),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    215
                )))),
            ),
            // L
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(220),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    220
                )))),
            ),
            // M
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(225)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(225),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // N
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(226),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    226
                )))),
            ),
            // O
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(301)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(301),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // P
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(304),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    304
                )))),
            ),
            // Q
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(310),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    310
                )))),
            ),
            // R
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::NoLayers,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(310)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(310),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // S
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::SecondLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(315)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(315),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // T1
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::SecondLayer,
                LayeredBoundsState::BothLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(320),
                    BoundInclusivity::Exclusive,
                ))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                    320
                )))),
            ),
            // T2
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::BothLayers,
                LayeredBoundsState::FirstLayer,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(320)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(320),
                    BoundInclusivity::Exclusive,
                ))),
            ),
            // U
            LayeredBoundsStateChangeAtRelativeBound::new(
                LayeredBoundsState::FirstLayer,
                LayeredBoundsState::NoLayers,
                Some(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(325)))),
                Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    Duration::hours(325),
                    BoundInclusivity::Exclusive,
                ))),
            ),
        ],
    );
}

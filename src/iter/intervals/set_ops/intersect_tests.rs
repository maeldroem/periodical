use chrono::Utc;

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::abridge::Abridgable;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::ops::IntersectionResult;
use crate::test_utils::date;

use super::intersect::*;

#[test]
fn peer_intersection_run() {
    // [--1--]   (-4-)(--5--)    [-7-]
    //   [2] [---3---]   [--6--]
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 4
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
        // 5
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
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
    ];

    assert_eq!(
        bounds.peer_intersection().collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
            ),
            // 2, 3
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
            ),
            // 3, 4
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
            // 4, 5
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
            // 5, 6
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 25),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 6, 7
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
            ),
            // 7,
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            ),
        ],
    );
}

#[test]
fn peer_intersection_with_run() {
    // [--1--]   (-4-)(--5--)    [-7-]
    //   [2] [---3---]   [--6--]
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 4
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
        // 5
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
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
    ];

    let custom_intersection_f = |a: &AbsoluteBounds, b: &AbsoluteBounds| -> IntersectionResult<AbsoluteBounds> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            IntersectionResult::Intersected(a.abridge(b))
        } else {
            IntersectionResult::Separate
        }
    };

    assert_eq!(
        bounds.peer_intersection_with(custom_intersection_f).collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
            ),
            // 2, 3
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 4))),
            ),
            // 3, 4
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
            // 4, 5
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            ),
            // 5, 6
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 25),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 6, 7
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
            ),
            // 7,
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            ),
        ],
    );
}

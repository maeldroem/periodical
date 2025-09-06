use chrono::Utc;

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::ops::DifferenceResult;
use crate::prelude::{EmptiableAbsoluteBounds, OverlapOrGapRemovalResult, RemovableOverlapOrGap};
use crate::test_utils::date;

use super::diff::*;

#[allow(clippy::too_many_lines)]
#[test]
fn peer_difference_run() {
    // [--1--]     [--4--]  [--6--]
    //   [2) [--3--]   [5)    [-7-]
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 14))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 15),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 23))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
    ];

    assert_eq!(
        bounds.peer_difference().collect::<Vec<_>>(),
        vec![
            // 1, 2
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 2),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                ))),
            ),
            // 2, 3
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 3),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 3, 4
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 10),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 4, 5
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 14),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                ))),
            ),
            // 5, 6
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 14))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 15),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 6, 7
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 23),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 7,
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 23))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
                )),
                None,
            ),
        ],
    );
}

#[allow(clippy::too_many_lines)]
#[test]
fn peer_difference_with_run() {
    // [--1--]     (--4--]  [--6--]
    //   [2) [--3--)   [5)    [-7-]
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 3),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 10),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 10),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 14))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 15),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 23))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
    ];

    let custom_difference_f = |a: &AbsoluteBounds, b: &AbsoluteBounds| -> DifferenceResult<EmptiableAbsoluteBounds> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            match a.remove_overlap_or_gap(b) {
                OverlapOrGapRemovalResult::Single(x) => DifferenceResult::Shrunk(x),
                OverlapOrGapRemovalResult::Split(x, y) => DifferenceResult::Split(x, y),
            }
        } else {
            DifferenceResult::Separate
        }
    };

    assert_eq!(
        bounds.peer_difference_with(custom_difference_f).collect::<Vec<_>>(),
        vec![
            // 1, 2
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 2),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                ))),
            ),
            // 2, 3
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 3),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 3, 4
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
                )),
                None,
            ),
            // 4, 5
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 10),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 14),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                ))),
            ),
            // 5, 6
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 14))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 15),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 6, 7
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 23),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                None,
            ),
            // 7,
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 23))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
                )),
                None,
            ),
        ],
    );
}

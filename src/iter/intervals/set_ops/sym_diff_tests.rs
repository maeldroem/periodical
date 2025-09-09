use chrono::Utc;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
use crate::ops::SymmetricDifferenceResult;
use crate::test_utils::date;

use super::sym_diff::*;

#[allow(clippy::too_many_lines)]
#[test]
fn peer_symmetric_difference_run() {
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
        bounds.peer_symmetric_difference().collect::<Vec<_>>(),
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
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
                ))),
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
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 10),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                ))),
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
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
                ))),
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
fn peer_symmetric_difference_with_run() {
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

    let custom_sym_diff_f =
        |a: &AbsoluteBounds, b: &AbsoluteBounds| -> SymmetricDifferenceResult<EmptiableAbsoluteBounds> {
            if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
                let diff_a_with_b = a.remove_overlap_or_gap(b);
                let diff_b_with_a = b.remove_overlap_or_gap(a);

                match (diff_a_with_b, diff_b_with_a) {
                    (
                        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
                        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
                    ) => SymmetricDifferenceResult::Single(EmptiableAbsoluteBounds::Empty),
                    (
                        OverlapOrGapRemovalResult::Single(single_diff),
                        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
                    )
                    | (
                        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
                        OverlapOrGapRemovalResult::Single(single_diff),
                    ) => SymmetricDifferenceResult::Single(single_diff),
                    (OverlapOrGapRemovalResult::Single(first), OverlapOrGapRemovalResult::Single(second)) => {
                        SymmetricDifferenceResult::Split(first, second)
                    },
                    (
                        OverlapOrGapRemovalResult::Split(split1, split2),
                        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
                    )
                    | (
                        OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBounds::Empty),
                        OverlapOrGapRemovalResult::Split(split1, split2),
                    ) => SymmetricDifferenceResult::Split(split1, split2),
                    _ => unreachable!(),
                }
            } else {
                SymmetricDifferenceResult::Separate
            }
        };

    assert_eq!(
        bounds
            .peer_symmetric_difference_with(custom_sym_diff_f)
            .collect::<Vec<_>>(),
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
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        date(&Utc, 2025, 1, 10),
                        BoundInclusivity::Exclusive,
                    )),
                ))),
            ),
            // 3, 4
            (
                EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
                )),
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                ))),
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
                Some(EmptiableAbsoluteBounds::Bound(AbsoluteBounds::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
                ))),
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

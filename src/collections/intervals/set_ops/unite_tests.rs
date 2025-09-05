use chrono::Utc;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::UnionResult;
use crate::prelude::{AbsoluteBounds, CanPositionOverlap, DEFAULT_OVERLAP_RULES, Extensible, OverlapRuleSet};
use crate::test_utils::date;

use super::unite::*;

#[test]
fn acc_union_run() {
    // [-1-] [3] [---4---)
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 8))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 16),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 1),
                BoundInclusivity::Exclusive,
            )),
        ),
    ];

    assert_eq!(
        bounds.acc_union().collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 1),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );
}

#[test]
fn acc_union_with_run() {
    // [-1-) [3] [---4---)     [-7-]
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 8))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 16),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 1),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
        ),
    ];

    let custom_union_f = |a: &AbsoluteBounds, b: &AbsoluteBounds| -> UnionResult<AbsoluteBounds> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            UnionResult::United(a.extend(b))
        } else {
            UnionResult::Separate
        }
    };

    assert_eq!(
        bounds.acc_union_with(custom_union_f).collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 1),
                    BoundInclusivity::Exclusive,
                )),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
            ),
        ],
    );
}

#[test]
fn peer_union_run() {
    // [-1-] [3] [---4---)
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 8))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 16),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 1),
                BoundInclusivity::Exclusive,
            )),
        ),
    ];

    assert_eq!(
        bounds.peer_union().collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            ),
            // 2, 3
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            ),
            // 3, 4
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 8))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
            ),
            // 4, 5
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 5, 6
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 16),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 20),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 6,
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 1),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );
}

#[allow(clippy::too_many_lines)]
#[test]
fn peer_union_with_run() {
    // [-1-) [3] [---4---)     [-7-]
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 2
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 5),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        // 3
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 8))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
        ),
        // 4
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 16),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 20),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 30),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 2, 1),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 7
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
        ),
    ];

    let custom_union_f = |a: &AbsoluteBounds, b: &AbsoluteBounds| -> UnionResult<AbsoluteBounds> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            UnionResult::United(a.extend(b))
        } else {
            UnionResult::Separate
        }
    };

    assert_eq!(
        bounds.peer_union_with(custom_union_f).collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            ),
            // 2, 3
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 5),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
            ),
            // 3, 4
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 8))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
            ),
            // 4, 5
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 5, 6
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 16),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 20),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 6, 7
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 1, 30),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    date(&Utc, 2025, 2, 1),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 7,
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
            ),
        ],
    );
}

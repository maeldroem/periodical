use std::error::Error;

use jiff::Zoned;

use super::sym_diff::*;
use crate::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
use crate::ops::SymmetricDifferenceResult;

#[allow(clippy::too_many_lines)]
#[test]
fn peer_symmetric_difference_run() -> Result<(), Box<dyn Error>> {
    // [--1--]     [--4--]  [--6--]
    //   [2) [--3--]   [5)    [-7-]
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    assert_eq!(
        bounds.peer_symmetric_difference().collect::<Vec<_>>(),
        vec![
            // 1, 2
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 2, 3
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 3, 4
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 4, 5
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 5, 6
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 6, 7
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
        ],
    );

    Ok(())
}

#[allow(clippy::too_many_lines)]
#[test]
fn peer_symmetric_difference_with_run() -> Result<(), Box<dyn Error>> {
    // [--1--]     (--4--]  [--6--]
    //   [2) [--3--)   [5)    [-7-]
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    let custom_sym_diff_f =
        |a: &AbsBoundPair, b: &AbsBoundPair| -> SymmetricDifferenceResult<EmptiableAbsBoundPair> {
            if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
                let diff_a_with_b = a.remove_overlap_or_gap(b);
                let diff_b_with_a = b.remove_overlap_or_gap(a);

                match (diff_a_with_b, diff_b_with_a) {
                    (
                        OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
                        OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
                    ) => SymmetricDifferenceResult::Single(EmptiableAbsBoundPair::Empty),
                    (
                        OverlapOrGapRemovalResult::Single(single_diff),
                        OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
                    )
                    | (
                        OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
                        OverlapOrGapRemovalResult::Single(single_diff),
                    ) => SymmetricDifferenceResult::Single(single_diff),
                    (OverlapOrGapRemovalResult::Single(first), OverlapOrGapRemovalResult::Single(second)) => {
                        SymmetricDifferenceResult::Split(first, second)
                    },
                    (
                        OverlapOrGapRemovalResult::Split(split1, split2),
                        OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
                    )
                    | (
                        OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
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
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 2, 3
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ))),
            ),
            // 3, 4
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 4, 5
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 5, 6
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 6, 7
            (
                EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_inclusivity(
                        "2025-01-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
        ],
    );

    Ok(())
}

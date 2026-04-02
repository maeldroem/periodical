use std::error::Error;

use jiff::Zoned;

use super::diff::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound, EmptiableAbsoluteBoundPair};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::intervals::ops::remove_overlap_or_gap::{OverlapOrGapRemovalResult, RemovableOverlapOrGap};
use crate::ops::DifferenceResult;

#[allow(clippy::too_many_lines)]
#[test]
fn peer_difference_run() -> Result<(), Box<dyn Error>> {
    // [--1--]     [--4--]  [--6--]
    //   [2) [--3--]   [5)    [-7-]
    let bounds = [
        // 1
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 2
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    assert_eq!(
        bounds.peer_difference().collect::<Vec<_>>(),
        vec![
            // 1, 2
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 2, 3
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
            // 3, 4
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
            // 4, 5
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 5, 6
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
            // 6, 7
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
fn peer_difference_with_run() -> Result<(), Box<dyn Error>> {
    // [--1--]     (--4--]  [--6--]
    //   [2) [--3--)   [5)    [-7-]
    let bounds = [
        // 1
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 2
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-23 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    let custom_difference_f =
        |a: &AbsoluteBoundPair, b: &AbsoluteBoundPair| -> DifferenceResult<EmptiableAbsoluteBoundPair> {
            if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
                match a.remove_overlap_or_gap(b) {
                    OverlapOrGapRemovalResult::Single(x) => DifferenceResult::Single(x),
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
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 2, 3
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
            // 3, 4
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                )),
                None,
            ),
            // 4, 5
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                Some(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound(),
                ))),
            ),
            // 5, 6
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-14 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                None,
            ),
            // 6, 7
            (
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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

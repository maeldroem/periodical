use std::error::Error;

use jiff::Zoned;

use super::intersect::*;
use crate::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::abridge::Abridgable;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::ops::IntersectionResult;

#[allow(clippy::too_many_lines)]
#[test]
fn peer_intersection_run() -> Result<(), Box<dyn Error>> {
    // [--1--]   (-4-)(--5--)    [-7-]
    //   [2] [---3---]   [--6--]
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    assert_eq!(
        bounds.peer_intersection().collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 2, 3
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 3, 4
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 4, 5
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 5, 6
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 6, 7
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ],
    );

    Ok(())
}

#[allow(clippy::too_many_lines)]
#[test]
fn peer_intersection_with_run() -> Result<(), Box<dyn Error>> {
    // [--1--]   (-4-)(--5--)    [-7-]
    //   [2] [---3---]   [--6--]
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
        ),
    ];

    let custom_intersection_f =
        |a: &AbsBoundPair, b: &AbsBoundPair| -> IntersectionResult<EmptiableAbsBoundPair> {
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
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
            // 2, 3
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
            // 3, 4
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            // 4, 5
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
            // 5, 6
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )),
            // 6, 7
            EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
        ],
    );

    Ok(())
}

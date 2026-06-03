use std::error::Error;

use jiff::Zoned;

use super::unite::*;
use crate::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::extend::Extensible;
use crate::intervals::ops::overlap::{CanPositionOverlap, DEFAULT_OVERLAP_RULES, OverlapRuleSet};
use crate::ops::UnionResult;

#[test]
fn acc_union_run() -> Result<(), Box<dyn Error>> {
    // [-1-] [3] [---4---)
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
    ];

    assert_eq!(
        bounds.acc_union().collect::<Vec<_>>(),
        vec![
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ],
    );

    Ok(())
}

#[test]
fn acc_union_with_run() -> Result<(), Box<dyn Error>> {
    // [-1-) [3] [---4---)     [-7-]
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
    ];

    let custom_union_f = |a: &AbsBoundPair, b: &AbsBoundPair| -> UnionResult<AbsBoundPair> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            todo!("uncomment when extend is fixed");
            // UnionResult::United(a.extend(b))
        } else {
            UnionResult::Separate
        }
    };

    assert_eq!(
        bounds.acc_union_with(custom_union_f).collect::<Vec<_>>(),
        vec![
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ],
    );

    Ok(())
}

#[allow(clippy::too_many_lines)]
#[test]
fn peer_union_run() -> Result<(), Box<dyn Error>> {
    // [-1-] [3] [---4---)
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
    ];

    assert_eq!(
        bounds.peer_union().collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 2, 3
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 3, 4
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 4, 5
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 5, 6
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ],
    );

    Ok(())
}

#[allow(clippy::too_many_lines)]
#[test]
fn peer_union_with_run() -> Result<(), Box<dyn Error>> {
    // [-1-) [3] [---4---)     [-7-]
    //     (--2--] (-5-) (-6-)
    let bounds = [
        // 1
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 2
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 3
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
        // 4
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 5
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 6
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        ),
        // 7
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound(),
            AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound(),
        ),
    ];

    let custom_union_f = |a: &AbsBoundPair, b: &AbsBoundPair| -> UnionResult<AbsBoundPair> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            todo!("uncomment when extend is fixed");
            // UnionResult::United(a.extend(b))
        } else {
            UnionResult::Separate
        }
    };

    assert_eq!(
        bounds.peer_union_with(custom_union_f).collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 2, 3
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 3, 4
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            // 4, 5
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 5, 6
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            // 6, 7
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ],
    );

    Ok(())
}

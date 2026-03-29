use std::error::Error;

use jiff::Zoned;

use super::unite::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
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
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 2
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
    ];

    assert_eq!(
        bounds.acc_union().collect::<Vec<_>>(),
        vec![
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
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
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 2
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 7
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
    ];

    let custom_union_f = |a: &AbsoluteBoundPair, b: &AbsoluteBoundPair| -> UnionResult<AbsoluteBoundPair> {
        if a.overlaps(b, OverlapRuleSet::VeryLenient, &DEFAULT_OVERLAP_RULES) {
            UnionResult::United(a.extend(b))
        } else {
            UnionResult::Separate
        }
    };

    assert_eq!(
        bounds.acc_union_with(custom_union_f).collect::<Vec<_>>(),
        vec![
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
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
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 2
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
    ];

    assert_eq!(
        bounds.peer_union().collect::<Vec<_>>(),
        vec![
            // 1, 2
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            ),
            // 2, 3
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            ),
            // 3, 4
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            ),
            // 4, 5
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 5, 6
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
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
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 2
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 3
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
        // 4
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 5
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 6
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
        ),
        // 7
        AbsoluteBoundPair::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )),
        ),
    ];

    let custom_union_f = |a: &AbsoluteBoundPair, b: &AbsoluteBoundPair| -> UnionResult<AbsoluteBoundPair> {
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
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            ),
            // 2, 3
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            ),
            // 3, 4
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-08 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            ),
            // 4, 5
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 5, 6
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-16 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
            // 6, 7
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ),
        ],
    );

    Ok(())
}

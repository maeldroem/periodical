use std::cmp::Ordering;
use std::error::Error;
use std::time::Duration;

use jiff::Timestamp;

use super::bound_pair::*;
use crate::intervals::absolute::{
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::special::UnboundedInterval;

#[test]
fn unchecked_new() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let abs_bounds = AbsBoundPair::unchecked_new(start, end);

    assert_eq!(abs_bounds.abs_start(), start);
    assert_eq!(abs_bounds.abs_end(), end);
    Ok(())
}

#[test]
fn new_should_swap() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let end = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_start_bound();
    let end = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let end = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_start_bound();
    let end = AbsFiniteBoundPos::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn from_range() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let range = start..;

    let bound_pair = AbsBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), AbsFiniteBoundPos::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), AbsEndBound::InfiniteFuture);
    Ok(())
}

#[test]
fn start_end() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let bound_pair = AbsBoundPair::new(start, end);

    assert_eq!(bound_pair.start(), start);
    assert_eq!(bound_pair.end(), end);

    Ok(())
}

#[test]
fn unchecked_set_start() -> Result<(), Box<dyn Error>> {
    let mut bounds = AbsBoundPair::new(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    let new_start = AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.abs_start(), new_start);
    Ok(())
}

#[test]
fn unchecked_set_end() -> Result<(), Box<dyn Error>> {
    let mut bounds = AbsBoundPair::new(
        AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    let new_end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.abs_end(), new_end);
    Ok(())
}

#[test]
fn set_start_chronological() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_start = AbsFiniteBoundPos::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(bounds.set_start(new_start));

    assert_eq!(bounds.abs_start(), new_start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

#[test]
fn set_start_unchronological() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_start = AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(!bounds.set_start(new_start));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

#[test]
fn set_end_chronological() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_end = AbsFiniteBoundPos::new("2025-01-02 08:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(bounds.set_end(new_end));

    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), new_end);
    Ok(())
}

#[test]
fn set_end_unchronological() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_end = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let mut bounds = AbsBoundPair::new(start, end);

    assert!(!bounds.set_end(new_end));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn less_start() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn greater_start() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn less_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn greater_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn equal_start_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_equal_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn equal_start_inf_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_inf_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_inf_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn equal_start_inf_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_inf_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }
}

#[test]
fn to_interval() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 08:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

    let bound_pair = AbsBoundPair::new(start.to_start_bound(), end.to_end_bound());

    assert_eq!(
        bound_pair.to_interval(),
        AbsInterval::Bounded(BoundedAbsInterval::new(start, end))
    );
    Ok(())
}

#[test]
fn to_emptiable_interval() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 08:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

    let bound_pair = AbsBoundPair::new(start.to_start_bound(), end.to_end_bound());

    assert_eq!(
        bound_pair.to_emptiable_interval(),
        EmptiableAbsInterval::Bound(AbsInterval::Bounded(BoundedAbsInterval::new(start, end)))
    );
    Ok(())
}

#[test]
fn to_emptiable() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(
        AbsBoundPair::new(start, end).to_emptiable(),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(start, end)),
    );
    Ok(())
}

#[test]
fn abs_start() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(AbsBoundPair::new(start, end).abs_start(), start);
    Ok(())
}

#[test]
fn abs_end() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(AbsBoundPair::new(start, end).abs_end(), end);
    Ok(())
}

#[test]
fn abs_bound_pair() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(
        AbsBoundPair::new(start, end).abs_bound_pair(),
        AbsBoundPair::new(start, end)
    );
    Ok(())
}

#[test]
fn duration() -> Result<(), Box<dyn Error>> {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert_eq!(
        bounded.duration(),
        IntervalDuration::Finite(Duration::from_hours(8), Epsilon::End)
    );
    assert_eq!(half_bounded.duration(), IntervalDuration::Infinite);
    assert_eq!(unbounded.duration(), IntervalDuration::Infinite);

    Ok(())
}

#[test]
fn openness() -> Result<(), Box<dyn Error>> {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded_to_past = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded_to_future = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsEndBound::InfiniteFuture,
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert_eq!(bounded.openness(), Openness::Bounded);
    assert_eq!(half_bounded_to_past.openness(), Openness::HalfBounded);
    assert_eq!(half_bounded_to_future.openness(), Openness::HalfBounded);
    assert_eq!(unbounded.openness(), Openness::Unbounded);

    Ok(())
}

#[test]
fn relativity() -> Result<(), Box<dyn Error>> {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert_eq!(bounded.relativity(), Relativity::Abs);
    assert_eq!(half_bounded.relativity(), Relativity::Abs);
    assert_eq!(unbounded.relativity(), Relativity::Any);

    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn unbounded_unbounded() {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_unbounded() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_after_first() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_before_first() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_before_first() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_after_first() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_before_first() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_after_first() -> Result<(), Box<dyn Error>> {
        let a = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        );
        let b = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2025-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }
}

#[test]
fn is_empty() -> Result<(), Box<dyn Error>> {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded = AbsBoundPair::new(
        AbsStartBound::InfinitePast,
        AbsFiniteBoundPos::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture);

    assert!(!bounded.is_empty());
    assert!(!half_bounded.is_empty());
    assert!(!unbounded.is_empty());

    Ok(())
}

#[test]
fn from_opt_timestamp_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        AbsBoundPair::from((Some(start), None)),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(start).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
    );
    Ok(())
}

#[test]
fn from_opt_timestamp_inclusivity_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        AbsBoundPair::from((
            Some((start, BoundInclusivity::Inclusive)),
            Some((end, BoundInclusivity::Exclusive))
        )),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_inclusivity(start, BoundInclusivity::Inclusive).to_start_bound(),
            AbsFiniteBoundPos::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound(),
        )
    );
    Ok(())
}

#[test]
fn from_bounded_absolute_interval() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

    let bounded = BoundedAbsInterval::new(start, end);

    assert_eq!(
        AbsBoundPair::from(bounded),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),),
    );

    Ok(())
}

#[test]
fn from_half_bounded_absolute_interval() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;

    let half_bounded = HalfBoundedAbsInterval::new_from_time(reference, OpeningDirection::ToFuture);

    assert_eq!(
        AbsBoundPair::from(half_bounded),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(reference).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
    );
    Ok(())
}

mod from_abs_interval {
    use super::*;

    #[test]
    fn from_abs_interval_bounded() -> Result<(), Box<dyn Error>> {
        let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

        let interval = BoundedAbsInterval::new(start, end).to_interval();

        assert_eq!(
            AbsBoundPair::from(interval),
            AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
        );

        Ok(())
    }

    #[test]
    fn from_abs_interval_half_bounded() -> Result<(), Box<dyn Error>> {
        let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;

        let interval = HalfBoundedAbsInterval::new_from_time(reference, OpeningDirection::ToFuture).to_interval();

        assert_eq!(
            AbsBoundPair::from(interval),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(reference).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            )
        );

        Ok(())
    }

    #[test]
    fn from_abs_interval_unbounded() {
        let interval = UnboundedInterval.to_abs_interval();

        assert_eq!(
            AbsBoundPair::from(interval),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
        );
    }
}

#[test]
fn try_from_emptiable_abs_bound_pair() {
    assert_eq!(
        AbsBoundPair::try_from(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        ))),
        Ok(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );
    assert_eq!(
        AbsBoundPair::try_from(EmptiableAbsBoundPair::Empty),
        Err(AbsBoundPairTryFromEmptiableAbsBoundPairError),
    );
}

mod try_from_emptiable_abs_interval {
    use super::*;
    use crate::prelude::EmptyInterval;

    #[test]
    fn not_empty() -> Result<(), Box<dyn Error>> {
        let start = AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new("2026-01-01 16:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

        let interval = BoundedAbsInterval::new(start, end).to_emptiable_interval();

        assert_eq!(
            AbsBoundPair::try_from(interval),
            Ok(AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),))
        );

        Ok(())
    }

    #[test]
    fn empty() {
        assert_eq!(
            AbsBoundPair::try_from(EmptiableAbsInterval::Empty(EmptyInterval)),
            Err(AbsBoundPairTryFromEmptiableAbsIntervalError)
        );
    }
}

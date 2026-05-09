use std::cmp::Ordering;
use std::error::Error;
use std::time::Duration;

use jiff::Timestamp;

use super::bound_pair::*;
use crate::intervals::absolute::{
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
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
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let abs_bounds = AbsoluteBoundPair::unchecked_new(start, end);

    assert_eq!(abs_bounds.abs_start(), start);
    assert_eq!(abs_bounds.abs_end(), end);
    Ok(())
}

#[test]
fn new_should_swap() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    Ok(())
}

#[test]
fn new_from_same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_start_bound();
    let end = AbsoluteFiniteBound::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    )
    .to_end_bound();

    let abs_bounds = AbsoluteBoundPair::new(start, end);

    assert_eq!(
        abs_bounds.abs_start(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        abs_bounds.abs_end(),
        AbsoluteFiniteBound::new_with_inclusivity(
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

    let bound_pair = AbsoluteBoundPair::from_range(range);

    assert_eq!(bound_pair.start(), AbsoluteFiniteBound::new(start).to_start_bound());
    assert_eq!(bound_pair.end(), AbsoluteEndBound::InfiniteFuture);
    Ok(())
}

#[test]
fn start_end() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let bound_pair = AbsoluteBoundPair::new(start, end);

    assert_eq!(bound_pair.start(), start);
    assert_eq!(bound_pair.end(), end);

    Ok(())
}

#[test]
fn unchecked_set_start() -> Result<(), Box<dyn Error>> {
    let mut bounds = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    let new_start = AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    bounds.unchecked_set_start(new_start);

    assert_eq!(bounds.abs_start(), new_start);
    Ok(())
}

#[test]
fn unchecked_set_end() -> Result<(), Box<dyn Error>> {
    let mut bounds = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );

    let new_end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    bounds.unchecked_set_end(new_end);

    assert_eq!(bounds.abs_end(), new_end);
    Ok(())
}

#[test]
fn set_start_chronological() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_start = AbsoluteFiniteBound::new("2025-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound();

    let mut bounds = AbsoluteBoundPair::new(start, end);

    assert!(bounds.set_start(new_start));

    assert_eq!(bounds.abs_start(), new_start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

#[test]
fn set_start_unchronological() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_start = AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    let mut bounds = AbsoluteBoundPair::new(start, end);

    assert!(!bounds.set_start(new_start));

    // Bounds should remain unchanged
    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), end);
    Ok(())
}

#[test]
fn set_end_chronological() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_end = AbsoluteFiniteBound::new("2025-01-02 08:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let mut bounds = AbsoluteBoundPair::new(start, end);

    assert!(bounds.set_end(new_end));

    assert_eq!(bounds.abs_start(), start);
    assert_eq!(bounds.abs_end(), new_end);
    Ok(())
}

#[test]
fn set_end_unchronological() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound();
    let new_end = AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    let mut bounds = AbsoluteBoundPair::new(start, end);

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
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn greater_start() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn less_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn greater_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn equal_start_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_equal_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn equal_start_inf_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_inf_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_inf_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn equal_start_inf_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
        let bound_pair2 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn equal_start_inf_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        let bound_pair2 = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
        let bound_pair2 = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }
}

#[test]
fn to_interval() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 08:00:00Z".parse::<Timestamp>()?;

    let bound_pair = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new(start).to_start_bound(),
        AbsoluteFiniteBound::new(end).to_end_bound(),
    );

    assert_eq!(
        bound_pair.to_interval(),
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(start, end))
    );
    Ok(())
}

#[test]
fn to_emptiable_interval() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 08:00:00Z".parse::<Timestamp>()?;

    let bound_pair = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new(start).to_start_bound(),
        AbsoluteFiniteBound::new(end).to_end_bound(),
    );

    assert_eq!(
        bound_pair.to_emptiable_interval(),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(start, end)))
    );
    Ok(())
}

#[test]
fn to_emptiable() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(
        AbsoluteBoundPair::new(start, end).to_emptiable(),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(start, end)),
    );
    Ok(())
}

#[test]
fn abs_start() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(AbsoluteBoundPair::new(start, end).abs_start(), start);
    Ok(())
}

#[test]
fn abs_end() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(AbsoluteBoundPair::new(start, end).abs_end(), end);
    Ok(())
}

#[test]
fn abs_bound_pair() -> Result<(), Box<dyn Error>> {
    let start = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();
    let end = AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(
        AbsoluteBoundPair::new(start, end).abs_bound_pair(),
        AbsoluteBoundPair::new(start, end)
    );
    Ok(())
}

#[test]
fn duration() -> Result<(), Box<dyn Error>> {
    let bounded = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

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
    let bounded = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded_to_past = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded_to_future = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
        AbsoluteEndBound::InfiniteFuture,
    );
    let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(bounded.openness(), Openness::Bounded);
    assert_eq!(half_bounded_to_past.openness(), Openness::HalfBounded);
    assert_eq!(half_bounded_to_future.openness(), Openness::HalfBounded);
    assert_eq!(unbounded.openness(), Openness::Unbounded);

    Ok(())
}

#[test]
fn relativity() -> Result<(), Box<dyn Error>> {
    let bounded = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert_eq!(bounded.relativity(), Relativity::Absolute);
    assert_eq!(half_bounded.relativity(), Relativity::Absolute);
    assert_eq!(unbounded.relativity(), Relativity::Any);

    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn unbounded_unbounded() {
        let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
        let b = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn unbounded_half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_unbounded() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_after_first() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_before_first() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_future_same_time_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );

        assert_eq!(a.cmp(&b), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_before_first() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_after_first() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_to_past_same_time_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new_with_inclusivity(
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
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new_with_inclusivity(
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
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new_with_inclusivity(
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
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new_with_inclusivity(
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
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn half_bounded_to_future_bounded_starts_after_first() -> Result<(), Box<dyn Error>> {
        let a = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        let b = AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );

        assert_eq!(a.cmp(&b), Ordering::Less);
        Ok(())
    }
}

#[test]
fn is_empty() -> Result<(), Box<dyn Error>> {
    let bounded = AbsoluteBoundPair::new(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 16:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let half_bounded = AbsoluteBoundPair::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

    assert!(!bounded.is_empty());
    assert!(!half_bounded.is_empty());
    assert!(!unbounded.is_empty());

    Ok(())
}

#[test]
fn from_opt_timestamp_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        AbsoluteBoundPair::from((Some(start), None)),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new(start).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture
        )
    );
    Ok(())
}

#[test]
fn from_opt_timestamp_inclusivity_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        AbsoluteBoundPair::from((
            Some((start, BoundInclusivity::Inclusive)),
            Some((end, BoundInclusivity::Exclusive))
        )),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(start, BoundInclusivity::Inclusive).to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound(),
        )
    );
    Ok(())
}

#[test]
fn from_bounded_absolute_interval() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;

    let bounded = BoundedAbsoluteInterval::new(start, end);

    assert_eq!(
        AbsoluteBoundPair::from(bounded),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new(start).to_start_bound(),
            AbsoluteFiniteBound::new(end).to_end_bound(),
        ),
    );

    Ok(())
}

#[test]
fn from_half_bounded_absolute_interval() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;

    let half_bounded = HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture);

    assert_eq!(
        AbsoluteBoundPair::from(half_bounded),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new(reference).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        )
    );
    Ok(())
}

mod from_abs_interval {
    use super::*;

    #[test]
    fn from_abs_interval_bounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;

        let interval = BoundedAbsoluteInterval::new(start, end).to_interval();

        assert_eq!(
            AbsoluteBoundPair::from(interval),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new(start).to_start_bound(),
                AbsoluteFiniteBound::new(end).to_end_bound(),
            )
        );

        Ok(())
    }

    #[test]
    fn from_abs_interval_half_bounded() -> Result<(), Box<dyn Error>> {
        let reference = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;

        let interval = HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture).to_interval();

        assert_eq!(
            AbsoluteBoundPair::from(interval),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new(reference).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            )
        );

        Ok(())
    }

    #[test]
    fn from_abs_interval_unbounded() {
        let interval = UnboundedInterval.to_abs_interval();

        assert_eq!(
            AbsoluteBoundPair::from(interval),
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
        );
    }
}

#[test]
fn try_from_emptiable_abs_bound_pair() {
    assert_eq!(
        AbsoluteBoundPair::try_from(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        ))),
        Ok(AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::InfiniteFuture,
        )),
    );
    assert_eq!(
        AbsoluteBoundPair::try_from(EmptiableAbsoluteBoundPair::Empty),
        Err(AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError),
    );
}

mod try_from_emptiable_abs_interval {
    use super::*;
    use crate::prelude::EmptyInterval;

    #[test]
    fn not_empty() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;

        let interval = BoundedAbsoluteInterval::new(start, end).to_emptiable_interval();

        assert_eq!(
            AbsoluteBoundPair::try_from(interval),
            Ok(AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new(start).to_start_bound(),
                AbsoluteFiniteBound::new(end).to_end_bound(),
            ))
        );

        Ok(())
    }

    #[test]
    fn empty() {
        assert_eq!(
            AbsoluteBoundPair::try_from(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Err(AbsoluteBoundPairTryFromEmptiableAbsoluteIntervalError)
        );
    }
}

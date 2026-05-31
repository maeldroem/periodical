use std::error::Error;
use std::ops::Bound;
use std::time::Duration;

use jiff::Timestamp;

use super::bounded_interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
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
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn unchecked_new() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::unchecked_new(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(interval.start_time(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

mod new {
    use super::*;

    #[test]
    fn no_swap() -> Result<(), Box<dyn Error>> {
        let interval = BoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.start_time(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn swap() -> Result<(), Box<dyn Error>> {
        let interval = BoundedAbsoluteInterval::new(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.start_time(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }
}

#[test]
fn unchecked_new_with_inclusivity() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start(), "2026-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

mod new_with_inclusivity {
    use super::*;

    #[test]
    fn no_swap() -> Result<(), Box<dyn Error>> {
        let interval = BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn swap() -> Result<(), Box<dyn Error>> {
        let interval = BoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range(start..=end),
            Ok(BoundedAbsoluteInterval::new(start, end))
        );

        Ok(())
    }

    #[test]
    fn included_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range(start..end),
            Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Inclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );

        Ok(())
    }

    #[test]
    fn included_unbounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range(start..),
            Err(BoundedAbsoluteIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn excluded_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Inclusive
            ))
        );

        Ok(())
    }

    #[test]
    fn excluded_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );

        Ok(())
    }

    #[test]
    fn excluded_unbounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Err(BoundedAbsoluteIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn unbounded_included() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range(..=end),
            Err(BoundedAbsoluteIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn unbounded_excluded() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from_range(..end),
            Err(BoundedAbsoluteIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from_range(..),
            Err(BoundedAbsoluteIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .start_time(),
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?
    );
    Ok(())
}

#[test]
fn end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .end_time(),
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );
    Ok(())
}

#[test]
fn start_inclusivity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .start_inclusivity(),
        BoundInclusivity::Exclusive
    );
    Ok(())
}

#[test]
fn end_inclusivity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .end_inclusivity(),
        BoundInclusivity::Exclusive
    );
    Ok(())
}

#[test]
fn unchecked_set_start() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_start("2025-01-03 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(interval.start(), "2025-01-03 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn unchecked_set_end() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-03 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_end("2025-01-01 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(interval.start(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

mod set_start {
    use super::*;

    #[test]
    fn set_start_less() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_start_time(new_start), Ok(()));
        assert_eq!(interval.start_time(), new_start);

        Ok(())
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive_by_moving_start_incl() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn set_start_equal_makes_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_start_time(new_start), Ok(()));
        assert_eq!(interval.start_time(), new_start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn set_start_greater_middle() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_start_time(new_start), Ok(()));
        assert_eq!(interval.start_time(), new_start);

        Ok(())
    }

    #[test]
    fn set_start_greater_after() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-03 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start_time(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);

        Ok(())
    }
}

mod set_end {
    use super::*;

    #[test]
    fn set_end_less_before() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_end_time(new_end),
            Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.end_time(), "2026-01-03 00:00:00Z".parse::<Timestamp>()?);

        Ok(())
    }

    #[test]
    fn set_end_less_middle() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_end_time(new_end), Ok(()));
        assert_eq!(interval.end_time(), new_end);

        Ok(())
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end(), "2026-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive_by_moving_end_incl() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end(), "2026-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn set_end_equal_makes_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_end_time(new_end), Ok(()));
        assert_eq!(interval.end_time(), new_end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn set_end_greater() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-03 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsoluteIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start_time(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);

        Ok(())
    }
}

#[test]
fn unchecked_set_start_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
    );

    interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start_time(), interval.end_time());
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn unchecked_set_end_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsoluteInterval::new(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
    );

    interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start_time(), interval.end_time());
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

mod set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_start_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn breaks_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_start_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }
}

mod set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_end_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn breaks_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_end_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedAbsoluteIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }
}

#[test]
fn to_interval() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::new(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(interval.clone().to_interval(), AbsoluteInterval::Bounded(interval));
    Ok(())
}

#[test]
fn to_emptiable_interval() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsoluteInterval::new(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(
        interval.clone().to_emptiable_interval(),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Bounded(interval))
    );
    Ok(())
}

#[test]
fn openness() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .openness(),
        Openness::Bounded
    );
    Ok(())
}

#[test]
fn relativity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .relativity(),
        Relativity::Absolute
    );
    Ok(())
}

#[test]
fn duration() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(24), Epsilon::Start)
    );
    Ok(())
}

#[test]
fn abs_bound_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .abs_bound_pair(),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
    );
    Ok(())
}

#[test]
fn abs_start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .abs_start(),
        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    Ok(())
}

#[test]
fn abs_end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .abs_end(),
        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );
    Ok(())
}

#[test]
fn emptiable_abs_bound_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .emptiable_abs_bound_pair(),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
        .to_emptiable()
    );
    Ok(())
}

#[test]
fn partial_abs_start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .partial_abs_start(),
        Some(AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound())
    );
    Ok(())
}

#[test]
fn partial_abs_end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .partial_abs_end(),
        Some(AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound())
    );
    Ok(())
}

#[test]
fn is_empty() -> Result<(), Box<dyn Error>> {
    assert!(
        !BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .is_empty()
    );
    Ok(())
}

#[test]
fn from_timestamp_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsoluteInterval::from((start, end)),
        BoundedAbsoluteInterval::new(start, end)
    );

    Ok(())
}

#[test]
fn from_timestamp_incl_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsoluteInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive))),
        BoundedAbsoluteInterval::new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive
        )
    );

    Ok(())
}

#[test]
fn from_range_included_excluded() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsoluteInterval::from(start..end),
        BoundedAbsoluteInterval::new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive
        )
    );
    Ok(())
}

#[test]
fn from_range_included_included() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsoluteInterval::from(start..=end),
        BoundedAbsoluteInterval::new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Inclusive
        ),
    );
    Ok(())
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new(start).to_start_bound(),
                AbsoluteFiniteBoundPosition::new(end).to_end_bound()
            )),
            Ok(BoundedAbsoluteInterval::new(start, end))
        );
        Ok(())
    }

    #[test]
    fn finite_infinite() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new(start).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )),
            Err(BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn infinite_finite() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new(end).to_end_bound()
            )),
            Err(BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            )),
            Err(BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_finite_finite() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new(start).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new(end).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(BoundedAbsoluteInterval::new(start, end))
        );
        Ok(())
    }

    #[test]
    fn bound_finite_infinite() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new(start).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn bound_infinite_finite() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsoluteInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new(end).to_end_bound()
                )
                .to_emptiable()
            ),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn bound_infinite_infinite() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(
                AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteBoundPairError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(EmptiableAbsoluteBoundPair::Empty),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        let bounded = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            BoundedAbsoluteInterval::try_from(bounded.clone().to_interval()),
            Ok(bounded)
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(
                HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
                .to_interval()
            ),
            Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(UnboundedInterval.to_abs_interval()),
            Err(BoundedAbsoluteIntervalFromAbsoluteIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        let bounded = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            BoundedAbsoluteInterval::try_from(bounded.clone().to_emptiable_interval()),
            Ok(bounded)
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(
                HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
                .to_emptiable_interval()
            ),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)
        );
        Ok(())
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(UnboundedInterval.to_emptiable_abs_interval()),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedAbsoluteInterval::try_from(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Err(BoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)
        );
    }
}

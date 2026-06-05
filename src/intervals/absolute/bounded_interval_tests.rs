use std::error::Error;
use std::ops::Bound;
use std::time::Duration;

use jiff::Timestamp;

use super::bounded_interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
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
    let interval = BoundedAbsInterval::unchecked_from_times(
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
        let interval = BoundedAbsInterval::from_times(
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
        let interval = BoundedAbsInterval::from_times(
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
    let interval = BoundedAbsInterval::unchecked_from_times_incl(
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start_time(), "2026-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end_time(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

mod new_with_inclusivity {
    use super::*;

    #[test]
    fn no_swap() -> Result<(), Box<dyn Error>> {
        let interval = BoundedAbsInterval::from_times_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start_time(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn swap() -> Result<(), Box<dyn Error>> {
        let interval = BoundedAbsInterval::from_times_incl(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start_time(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
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
            BoundedAbsInterval::try_from_range(start..=end),
            Ok(BoundedAbsInterval::from_times(start, end))
        );

        Ok(())
    }

    #[test]
    fn included_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from_range(start..end),
            Ok(BoundedAbsInterval::from_times_incl(
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
            BoundedAbsInterval::try_from_range(start..),
            Err(BoundedAbsIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn excluded_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Ok(BoundedAbsInterval::from_times_incl(
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
            BoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Ok(BoundedAbsInterval::from_times_incl(
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
            BoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Err(BoundedAbsIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn unbounded_included() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from_range(..=end),
            Err(BoundedAbsIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn unbounded_excluded() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from_range(..end),
            Err(BoundedAbsIntervalTryFromRangeError)
        );

        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            BoundedAbsInterval::try_from_range(..),
            Err(BoundedAbsIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
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
        BoundedAbsInterval::from_times(
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
        BoundedAbsInterval::from_times_incl(
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
        BoundedAbsInterval::from_times_incl(
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
    let mut interval = BoundedAbsInterval::from_times_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_start_time("2025-01-03 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(interval.start_time(), "2025-01-03 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn unchecked_set_end() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsInterval::from_times_incl(
        "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        "2025-01-03 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_end_time("2025-01-01 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(interval.start_time(), "2025-01-02 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.end_time(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

mod set_start {
    use super::*;

    #[test]
    fn set_start_less() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsInterval::from_times(
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

        let mut interval = BoundedAbsInterval::from_times_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_time(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive_by_moving_start_incl() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsInterval::from_times_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_time(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn set_start_equal_makes_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let new_start = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsInterval::from_times(
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

        let mut interval = BoundedAbsInterval::from_times(
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

        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
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

        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_end_time(new_end),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.end_time(), "2026-01-03 00:00:00Z".parse::<Timestamp>()?);

        Ok(())
    }

    #[test]
    fn set_end_less_middle() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsInterval::from_times(
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

        let mut interval = BoundedAbsInterval::from_times_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_end_time(new_end),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_time(), "2026-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive_by_moving_end_incl() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsInterval::from_times_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_end_time(new_end),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_time(), "2026-01-02 00:00:00Z".parse::<Timestamp>()?);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn set_end_equal_makes_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let new_end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        let mut interval = BoundedAbsInterval::from_times(
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

        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start_time(), "2026-01-01 00:00:00Z".parse::<Timestamp>()?);

        Ok(())
    }
}

#[test]
fn unchecked_set_start_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = BoundedAbsInterval::from_times(
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
    let mut interval = BoundedAbsInterval::from_times(
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
        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_start_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn breaks_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_start_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }
}

mod set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(interval.set_end_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);

        Ok(())
    }

    #[test]
    fn breaks_doubly_inclusive() -> Result<(), Box<dyn Error>> {
        let mut interval = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            interval.set_end_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);

        Ok(())
    }
}

#[test]
fn to_interval() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::from_times(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(interval.clone().to_interval(), AbsInterval::Bounded(interval));
    Ok(())
}

#[test]
fn to_emptiable_interval() -> Result<(), Box<dyn Error>> {
    let interval = BoundedAbsInterval::from_times(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );

    assert_eq!(
        interval.clone().to_emptiable_interval(),
        EmptiableAbsInterval::Bound(AbsInterval::Bounded(interval))
    );
    Ok(())
}

#[test]
fn openness() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
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
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .relativity(),
        Relativity::Abs
    );
    Ok(())
}

#[test]
fn duration() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times_incl(
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
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
    );
    Ok(())
}

#[test]
fn abs_start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )
        .abs_start(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    Ok(())
}

#[test]
fn abs_end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .abs_end(),
        AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );
    Ok(())
}

#[test]
fn emptiable_abs_bound_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .emptiable_abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
        .to_emptiable()
    );
    Ok(())
}

#[test]
fn partial_abs_start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .partial_abs_start(),
        Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound())
    );
    Ok(())
}

#[test]
fn partial_abs_end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        )
        .partial_abs_end(),
        Some(AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound())
    );
    Ok(())
}

#[test]
fn is_empty() -> Result<(), Box<dyn Error>> {
    assert!(
        !BoundedAbsInterval::from_times(
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
        BoundedAbsInterval::from((start, end)),
        BoundedAbsInterval::from_times(start, end)
    );

    Ok(())
}

#[test]
fn from_timestamp_incl_pair() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive))),
        BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive)
    );

    Ok(())
}

#[test]
fn from_range_included_excluded() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsInterval::from(start..end),
        BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive)
    );
    Ok(())
}

#[test]
fn from_range_included_included() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let end = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        BoundedAbsInterval::from(start..=end),
        BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Inclusive),
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
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(start).to_start_bound(),
                AbsFiniteBoundPos::new(end).to_end_bound()
            )),
            Ok(BoundedAbsInterval::from_times(start, end))
        );
        Ok(())
    }

    #[test]
    fn finite_infinite() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(start).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            Err(BoundedAbsIntervalTryFromAbsBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn infinite_finite() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(end).to_end_bound()
            )),
            Err(BoundedAbsIntervalTryFromAbsBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            Err(BoundedAbsIntervalTryFromAbsBoundPairError)
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
            BoundedAbsInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(start).to_start_bound(),
                    AbsFiniteBoundPos::new(end).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(BoundedAbsInterval::from_times(start, end))
        );
        Ok(())
    }

    #[test]
    fn bound_finite_infinite() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(start).to_start_bound(),
                    AbsEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Err(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn bound_infinite_finite() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            BoundedAbsInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsFiniteBoundPos::new(end).to_end_bound())
                    .to_emptiable()
            ),
            Err(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn bound_infinite_infinite() {
        assert_eq!(
            BoundedAbsInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            Err(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedAbsInterval::try_from(EmptiableAbsBoundPair::Empty),
            Err(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        let bounded = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(BoundedAbsInterval::try_from(bounded.clone().to_interval()), Ok(bounded));
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsInterval::try_from(
                HalfBoundedAbsInterval::from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
                .to_interval()
            ),
            Err(BoundedAbsIntervalFromAbsIntervalError)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            BoundedAbsInterval::try_from(UnboundedInterval.to_abs_interval()),
            Err(BoundedAbsIntervalFromAbsIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        let bounded = BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            BoundedAbsInterval::try_from(bounded.clone().to_emptiable_interval()),
            Ok(bounded)
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsInterval::try_from(
                HalfBoundedAbsInterval::from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
                .to_emptiable_interval()
            ),
            Err(BoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
        Ok(())
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            BoundedAbsInterval::try_from(UnboundedInterval.to_emptiable_abs_interval()),
            Err(BoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedAbsInterval::try_from(EmptiableAbsInterval::Empty(EmptyInterval)),
            Err(BoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
    }
}

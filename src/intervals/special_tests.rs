use std::error::Error;
use std::time::Duration as StdDuration;

use jiff::{SignedDuration, Timestamp};

use super::special::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    IsEmpty,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};

mod unbounded_interval {
    use super::*;

    #[test]
    fn to_abs_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn to_emptiable_abs_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_emptiable_abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn to_abs_interval() {
        assert_eq!(
            UnboundedInterval.to_abs_interval(),
            AbsInterval::Unbounded(UnboundedInterval)
        );
    }

    #[test]
    fn to_emptiable_abs_interval() {
        assert_eq!(
            UnboundedInterval.to_emptiable_abs_interval(),
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn to_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_rel_bound_pair(),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn to_emptiable_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_emptiable_rel_bound_pair(),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn to_rel_interval() {
        assert_eq!(
            UnboundedInterval.to_rel_interval(),
            RelInterval::Unbounded(UnboundedInterval)
        );
    }

    #[test]
    fn to_emptiable_rel_interval() {
        assert_eq!(
            UnboundedInterval.to_emptiable_rel_interval(),
            RelInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn openness() {
        assert_eq!(UnboundedInterval.openness(), Openness::Unbounded);
    }

    #[test]
    fn relativity() {
        assert_eq!(UnboundedInterval.relativity(), Relativity::Any);
    }

    #[test]
    fn duration() {
        assert_eq!(UnboundedInterval.duration(), IntervalDuration::Infinite);
    }

    #[test]
    fn abs_bound_pair() {
        assert_eq!(
            UnboundedInterval.abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        );
    }

    #[test]
    fn abs_start() {
        assert_eq!(UnboundedInterval.abs_start(), AbsStartBound::InfinitePast);
    }

    #[test]
    fn abs_end() {
        assert_eq!(UnboundedInterval.abs_end(), AbsEndBound::InfiniteFuture);
    }

    #[test]
    fn rel_bound_pair() {
        assert_eq!(
            UnboundedInterval.rel_bound_pair(),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        );
    }

    #[test]
    fn rel_start() {
        assert_eq!(UnboundedInterval.rel_start(), RelStartBound::InfinitePast);
    }

    #[test]
    fn rel_end() {
        assert_eq!(UnboundedInterval.rel_end(), RelEndBound::InfiniteFuture);
    }

    #[test]
    fn from_range_full() {
        assert_eq!(UnboundedInterval::from(..), UnboundedInterval);
    }

    #[test]
    fn try_from_abs_bound_pair() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            Err(UnboundedIntervalTryFromAbsBoundPairError)
        );

        Ok(())
    }

    #[test]
    fn try_from_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )),
            Err(UnboundedIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn try_from_emptiable_abs_bound_pair() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Err(UnboundedIntervalTryFromEmptiableAbsBoundPairError)
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableAbsBoundPair::Empty),
            Err(UnboundedIntervalTryFromEmptiableAbsBoundPairError)
        );

        Ok(())
    }

    #[test]
    fn try_from_emptiable_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval::try_from(
                RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
            ),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
                RelEndBound::InfiniteFuture
            )),
            Err(UnboundedIntervalTryFromRelBoundPairError)
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableRelBoundPair::Empty),
            Err(UnboundedIntervalTryFromEmptiableRelBoundPairError)
        );
    }

    #[test]
    fn try_from_abs_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(AbsInterval::Unbounded(UnboundedInterval)),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))),
            Err(UnboundedIntervalTryFromAbsIntervalError),
        );

        Ok(())
    }

    #[test]
    fn try_from_rel_interval() {
        assert_eq!(
            UnboundedInterval::try_from(RelInterval::Unbounded(UnboundedInterval)),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(RelInterval::Bounded(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(5),
            ))),
            Err(UnboundedIntervalTryFromRelIntervalError),
        );
    }

    #[test]
    fn try_from_emptiable_abs_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(
                AbsInterval::Bounded(BoundedAbsInterval::from_times(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
                ))
                .to_emptiable()
            ),
            Err(UnboundedIntervalTryFromEmptiableAbsIntervalError),
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableAbsInterval::Empty(EmptyInterval)),
            Err(UnboundedIntervalTryFromEmptiableAbsIntervalError)
        );

        Ok(())
    }

    #[test]
    fn try_from_emptiable_rel_interval() {
        assert_eq!(
            UnboundedInterval::try_from(RelInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(
                RelInterval::Bounded(BoundedRelInterval::from_offsets(
                    SignedDuration::from_hours(2),
                    SignedDuration::from_hours(8)
                ))
                .to_emptiable()
            ),
            Err(UnboundedIntervalTryFromEmptiableRelIntervalError),
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableRelInterval::Empty(EmptyInterval)),
            Err(UnboundedIntervalTryFromEmptiableRelIntervalError)
        );
    }
}

mod empty_interval {
    use super::*;

    #[test]
    fn to_emptiable_abs_bound_pair() {
        assert_eq!(
            EmptyInterval.to_emptiable_abs_bound_pair(),
            EmptiableAbsBoundPair::Empty
        );
    }

    #[test]
    fn to_emptiable_abs_interval() {
        assert_eq!(
            EmptyInterval.to_emptiable_abs_interval(),
            EmptiableAbsInterval::Empty(EmptyInterval)
        );
    }

    #[test]
    fn to_emptiable_rel_bound_pair() {
        assert_eq!(
            EmptyInterval.to_emptiable_rel_bound_pair(),
            EmptiableRelBoundPair::Empty
        );
    }

    #[test]
    fn to_emptiable_rel_interval() {
        assert_eq!(
            EmptyInterval.to_emptiable_rel_interval(),
            EmptiableRelInterval::Empty(EmptyInterval)
        );
    }

    #[test]
    fn openness() {
        assert_eq!(EmptyInterval.openness(), Openness::Empty);
    }

    #[test]
    fn relativity() {
        assert_eq!(EmptyInterval.relativity(), Relativity::Any);
    }

    #[test]
    fn duration() {
        assert_eq!(
            EmptyInterval.duration(),
            IntervalDuration::Finite(StdDuration::ZERO, Epsilon::None)
        );
    }

    #[test]
    fn emptiable_abs_bound_pair() {
        assert_eq!(EmptyInterval.emptiable_abs_bound_pair(), EmptiableAbsBoundPair::Empty);
    }

    #[test]
    fn partial_abs_start() {
        assert!(EmptyInterval.partial_abs_start().is_none());
    }

    #[test]
    fn partial_abs_end() {
        assert!(EmptyInterval.partial_abs_end().is_none());
    }

    #[test]
    fn emptiable_rel_bound_pair() {
        assert_eq!(EmptyInterval.emptiable_rel_bound_pair(), EmptiableRelBoundPair::Empty);
    }

    #[test]
    fn partial_rel_start() {
        assert!(EmptyInterval.partial_rel_start().is_none());
    }

    #[test]
    fn partial_rel_end() {
        assert!(EmptyInterval.partial_rel_end().is_none());
    }

    #[test]
    fn is_empty() {
        assert!(EmptyInterval.is_empty());
    }

    #[test]
    fn try_from_emptiable_abs_bound_pair() {
        assert_eq!(EmptyInterval::try_from(EmptiableAbsBoundPair::Empty), Ok(EmptyInterval),);
        assert_eq!(
            EmptyInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            Err(EmptyIntervalTryFromEmptiableAbsBoundPair)
        );
    }

    #[test]
    fn try_from_emptiable_abs_interval() {
        assert_eq!(
            EmptyInterval::try_from(EmptiableAbsInterval::Empty(EmptyInterval)),
            Ok(EmptyInterval)
        );
        assert_eq!(
            EmptyInterval::try_from(EmptiableAbsInterval::Bound(AbsInterval::Unbounded(UnboundedInterval))),
            Err(EmptyIntervalTryFromEmptiableAbsInterval),
        );
    }

    #[test]
    fn try_from_emptiable_rel_bound_pair() {
        assert_eq!(EmptyInterval::try_from(EmptiableRelBoundPair::Empty), Ok(EmptyInterval),);
        assert_eq!(
            EmptyInterval::try_from(
                RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
            ),
            Err(EmptyIntervalTryFromEmptiableRelBoundPair)
        );
    }

    #[test]
    fn try_from_emptiable_rel_interval() {
        assert_eq!(
            EmptyInterval::try_from(EmptiableRelInterval::Empty(EmptyInterval)),
            Ok(EmptyInterval)
        );
        assert_eq!(
            EmptyInterval::try_from(EmptiableRelInterval::Bound(RelInterval::Unbounded(UnboundedInterval))),
            Err(EmptyIntervalTryFromEmptiableRelInterval),
        );
    }
}

use std::error::Error;
use std::time::Duration as StdDuration;

use jiff::{SignedDuration, Timestamp};

use super::special::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
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
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeInterval,
    RelativeStartBound,
};

mod unbounded_interval {
    use super::*;

    #[test]
    fn to_abs_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_abs_bound_pair(),
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn to_emptiable_abs_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn to_abs_interval() {
        assert_eq!(
            UnboundedInterval.to_abs_interval(),
            AbsoluteInterval::Unbounded(UnboundedInterval)
        );
    }

    #[test]
    fn to_emptiable_abs_interval() {
        assert_eq!(
            UnboundedInterval.to_emptiable_abs_interval(),
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn to_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_rel_bound_pair(),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn to_emptiable_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval.to_emptiable_rel_bound_pair(),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn to_rel_interval() {
        assert_eq!(
            UnboundedInterval.to_rel_interval(),
            RelativeInterval::Unbounded(UnboundedInterval)
        );
    }

    #[test]
    fn to_emptiable_rel_interval() {
        assert_eq!(
            UnboundedInterval.to_emptiable_rel_interval(),
            RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()
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
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
        );
    }

    #[test]
    fn abs_start() {
        assert_eq!(UnboundedInterval.abs_start(), AbsoluteStartBound::InfinitePast);
    }

    #[test]
    fn abs_end() {
        assert_eq!(UnboundedInterval.abs_end(), AbsoluteEndBound::InfiniteFuture);
    }

    #[test]
    fn rel_bound_pair() {
        assert_eq!(
            UnboundedInterval.rel_bound_pair(),
            RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
        );
    }

    #[test]
    fn rel_start() {
        assert_eq!(UnboundedInterval.rel_start(), RelativeStartBound::InfinitePast);
    }

    #[test]
    fn rel_end() {
        assert_eq!(UnboundedInterval.rel_end(), RelativeEndBound::InfiniteFuture);
    }

    #[test]
    fn from_range_full() {
        assert_eq!(UnboundedInterval::from(..), UnboundedInterval);
    }

    #[test]
    fn try_from_abs_bound_pair() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            )),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )),
            Err(UnboundedIntervalTryFromAbsoluteBoundPairError)
        );

        Ok(())
    }

    #[test]
    fn try_from_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval::try_from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::InfiniteFuture
            )),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )),
            Err(UnboundedIntervalTryFromRelativeBoundPairError)
        );
    }

    #[test]
    fn try_from_emptiable_abs_bound_pair() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(
                AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Err(UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError)
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableAbsoluteBoundPair::Empty),
            Err(UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError)
        );

        Ok(())
    }

    #[test]
    fn try_from_emptiable_rel_bound_pair() {
        assert_eq!(
            UnboundedInterval::try_from(
                RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Ok(UnboundedInterval)
        );
        assert_eq!(
            UnboundedInterval::try_from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )),
            Err(UnboundedIntervalTryFromRelativeBoundPairError)
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableRelativeBoundPair::Empty),
            Err(UnboundedIntervalTryFromEmptiableRelativeBoundPairError)
        );
    }

    #[test]
    fn try_from_abs_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval)),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))),
            Err(UnboundedIntervalTryFromAbsoluteIntervalError),
        );

        Ok(())
    }

    #[test]
    fn try_from_rel_interval() {
        assert_eq!(
            UnboundedInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval)),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(RelativeInterval::Bounded(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(5),
            ))),
            Err(UnboundedIntervalTryFromRelativeIntervalError),
        );
    }

    #[test]
    fn try_from_emptiable_abs_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval::try_from(AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
                ))
                .to_emptiable()
            ),
            Err(UnboundedIntervalTryFromEmptiableAbsoluteIntervalError),
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Err(UnboundedIntervalTryFromEmptiableAbsoluteIntervalError)
        );

        Ok(())
    }

    #[test]
    fn try_from_emptiable_rel_interval() {
        assert_eq!(
            UnboundedInterval::try_from(RelativeInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ok(UnboundedInterval),
        );
        assert_eq!(
            UnboundedInterval::try_from(
                RelativeInterval::Bounded(BoundedRelativeInterval::new(
                    SignedDuration::from_hours(2),
                    SignedDuration::from_hours(8)
                ))
                .to_emptiable()
            ),
            Err(UnboundedIntervalTryFromEmptiableRelativeIntervalError),
        );
        assert_eq!(
            UnboundedInterval::try_from(EmptiableRelativeInterval::Empty(EmptyInterval)),
            Err(UnboundedIntervalTryFromEmptiableRelativeIntervalError)
        );
    }
}

mod empty_interval {
    use super::*;

    #[test]
    fn to_emptiable_abs_bound_pair() {
        assert_eq!(
            EmptyInterval.to_emptiable_abs_bound_pair(),
            EmptiableAbsoluteBoundPair::Empty
        );
    }

    #[test]
    fn to_emptiable_abs_interval() {
        assert_eq!(
            EmptyInterval.to_emptiable_abs_interval(),
            EmptiableAbsoluteInterval::Empty(EmptyInterval)
        );
    }

    #[test]
    fn to_emptiable_rel_bound_pair() {
        assert_eq!(
            EmptyInterval.to_emptiable_rel_bound_pair(),
            EmptiableRelativeBoundPair::Empty
        );
    }

    #[test]
    fn to_emptiable_rel_interval() {
        assert_eq!(
            EmptyInterval.to_emptiable_rel_interval(),
            EmptiableRelativeInterval::Empty(EmptyInterval)
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
        assert_eq!(
            EmptyInterval.emptiable_abs_bound_pair(),
            EmptiableAbsoluteBoundPair::Empty
        );
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
        assert_eq!(
            EmptyInterval.emptiable_rel_bound_pair(),
            EmptiableRelativeBoundPair::Empty
        );
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
        assert_eq!(
            EmptyInterval::try_from(EmptiableAbsoluteBoundPair::Empty),
            Ok(EmptyInterval),
        );
        assert_eq!(
            EmptyInterval::try_from(
                AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Err(EmptyIntervalTryFromEmptiableAbsoluteBoundPair)
        );
    }

    #[test]
    fn try_from_emptiable_abs_interval() {
        assert_eq!(
            EmptyInterval::try_from(EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ok(EmptyInterval)
        );
        assert_eq!(
            EmptyInterval::try_from(EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Unbounded(
                UnboundedInterval
            ))),
            Err(EmptyIntervalTryFromEmptiableAbsoluteInterval),
        );
    }

    #[test]
    fn try_from_emptiable_rel_bound_pair() {
        assert_eq!(
            EmptyInterval::try_from(EmptiableRelativeBoundPair::Empty),
            Ok(EmptyInterval),
        );
        assert_eq!(
            EmptyInterval::try_from(
                RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Err(EmptyIntervalTryFromEmptiableRelativeBoundPair)
        );
    }

    #[test]
    fn try_from_emptiable_rel_interval() {
        assert_eq!(
            EmptyInterval::try_from(EmptiableRelativeInterval::Empty(EmptyInterval)),
            Ok(EmptyInterval)
        );
        assert_eq!(
            EmptyInterval::try_from(EmptiableRelativeInterval::Bound(RelativeInterval::Unbounded(
                UnboundedInterval
            ))),
            Err(EmptyIntervalTryFromEmptiableRelativeInterval),
        );
    }
}

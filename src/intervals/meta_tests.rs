use std::ops::Bound;
use std::time::Duration as StdDuration;

use super::meta::*;

mod opening_direction {
    use super::*;

    #[test]
    fn from_bool() {
        assert_eq!(OpeningDirection::from(true), OpeningDirection::ToFuture);
        assert_eq!(OpeningDirection::from(false), OpeningDirection::ToPast);
    }

    #[test]
    fn opposite() {
        assert_eq!(OpeningDirection::ToFuture.opposite(), OpeningDirection::ToPast);
        assert_eq!(OpeningDirection::ToPast.opposite(), OpeningDirection::ToFuture);
    }
}

mod epsilon {
    use super::*;

    #[test]
    fn has_epsilon() {
        assert!(!Epsilon::None.has_epsilon());
        assert!(Epsilon::Start.has_epsilon());
        assert!(Epsilon::End.has_epsilon());
        assert!(Epsilon::Both.has_epsilon());
    }

    #[test]
    fn has_epsilon_on_start() {
        assert!(!Epsilon::None.has_epsilon_on_start());
        assert!(Epsilon::Start.has_epsilon_on_start());
        assert!(!Epsilon::End.has_epsilon_on_start());
        assert!(Epsilon::Both.has_epsilon_on_start());
    }

    #[test]
    fn has_epsilon_on_end() {
        assert!(!Epsilon::None.has_epsilon_on_end());
        assert!(!Epsilon::Start.has_epsilon_on_end());
        assert!(Epsilon::End.has_epsilon_on_end());
        assert!(Epsilon::Both.has_epsilon_on_end());
    }

    #[test]
    fn interpret_as_duration_bound_specific() {
        assert_eq!(
            Epsilon::None.interpret_as_duration_bound_specific(StdDuration::from_secs(1), StdDuration::from_secs(2)),
            Ok(StdDuration::ZERO),
        );
        assert_eq!(
            Epsilon::Start.interpret_as_duration_bound_specific(StdDuration::from_secs(1), StdDuration::from_secs(2)),
            Ok(StdDuration::from_secs(1)),
        );
        assert_eq!(
            Epsilon::End.interpret_as_duration_bound_specific(StdDuration::from_secs(1), StdDuration::from_secs(2)),
            Ok(StdDuration::from_secs(2)),
        );
        assert_eq!(
            Epsilon::Both.interpret_as_duration_bound_specific(StdDuration::from_secs(1), StdDuration::from_secs(2)),
            Ok(StdDuration::from_secs(3)),
        );
    }

    #[test]
    fn interpret_as_duration() {
        assert_eq!(
            Epsilon::None.interpret_as_duration(StdDuration::from_secs(1)),
            Ok(StdDuration::ZERO)
        );
        assert_eq!(
            Epsilon::Start.interpret_as_duration(StdDuration::from_secs(1)),
            Ok(StdDuration::from_secs(1))
        );
        assert_eq!(
            Epsilon::End.interpret_as_duration(StdDuration::from_secs(1)),
            Ok(StdDuration::from_secs(1))
        );
        assert_eq!(
            Epsilon::Both.interpret_as_duration(StdDuration::from_secs(1)),
            Ok(StdDuration::from_secs(2))
        );
    }

    #[test]
    fn from_bound_inclusivity_pair() {
        assert_eq!(
            Epsilon::from((BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)),
            Epsilon::None
        );
        assert_eq!(
            Epsilon::from((BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)),
            Epsilon::Start
        );
        assert_eq!(
            Epsilon::from((BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)),
            Epsilon::End
        );
        assert_eq!(
            Epsilon::from((BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)),
            Epsilon::Both
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn is_finite() {
        assert!(Duration::Finite(StdDuration::ZERO, Epsilon::None).is_finite());
        assert!(!Duration::Infinite.is_finite());
    }

    #[test]
    fn finite() {
        assert_eq!(
            Duration::Finite(StdDuration::from_hours(2), Epsilon::End).finite(),
            Some((StdDuration::from_hours(2), Epsilon::End)),
        );
        assert_eq!(Duration::Infinite.finite(), None);
    }

    #[test]
    fn finite_interpret_duration_on_finite() {
        assert_eq!(
            Duration::Finite(StdDuration::from_hours(1), Epsilon::End)
                .finite_interpret_epsilon(StdDuration::from_secs(1)),
            Some(StdDuration::from_mins(59) + StdDuration::from_secs(59)),
        );
    }

    #[test]
    fn finite_interpret_duration_on_infinite() {
        assert_eq!(
            Duration::Infinite.finite_interpret_epsilon(StdDuration::from_secs(1)),
            None,
        );
    }

    #[test]
    fn finite_interpret_duration_on_finite_large_epsilon() {
        assert_eq!(
            Duration::Finite(StdDuration::from_hours(1), Epsilon::Start)
                .finite_interpret_epsilon(StdDuration::from_hours(2)),
            Some(StdDuration::ZERO),
        );
    }

    #[test]
    fn finite_strip_epsilon_finite() {
        assert_eq!(
            Duration::Finite(StdDuration::from_hours(2), Epsilon::Both).finite_strip_epsilon(),
            Some(StdDuration::from_hours(2)),
        );
    }

    #[test]
    fn finite_strip_epsilon_infinite() {
        assert_eq!(Duration::Infinite.finite_strip_epsilon(), None);
    }

    #[test]
    fn from_duration() {
        assert_eq!(
            Duration::from(StdDuration::ZERO),
            Duration::Finite(StdDuration::ZERO, Epsilon::default())
        );
    }

    #[test]
    fn from_duration_and_epsilon() {
        assert_eq!(
            Duration::from((StdDuration::from_hours(2), Epsilon::End)),
            Duration::Finite(StdDuration::from_hours(2), Epsilon::End),
        );
    }
}

mod bound_inclusivity {
    use super::*;

    #[test]
    fn default() {
        assert_eq!(BoundInclusivity::default(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn to_range_bound_with() {
        assert_eq!(BoundInclusivity::Inclusive.to_range_bound_with(1), Bound::Included(1));
        assert_eq!(BoundInclusivity::Exclusive.to_range_bound_with(1), Bound::Excluded(1));
    }

    #[test]
    fn from_bool() {
        assert_eq!(BoundInclusivity::from(true), BoundInclusivity::Inclusive);
        assert_eq!(BoundInclusivity::from(false), BoundInclusivity::Exclusive);
    }
}

mod bound_extremality {
    use super::*;

    #[test]
    fn opposite() {
        assert_eq!(BoundExtremality::Start.opposite(), BoundExtremality::End);
        assert_eq!(BoundExtremality::End.opposite(), BoundExtremality::Start);
    }
}

mod interval_type {
    use super::*;

    mod try_with_rel {
        use super::*;

        #[test]
        fn bounded() {
            assert_eq!(
                IntervalType::Bounded.try_with_rel(Relativity::Absolute),
                Ok(IntervalTypeWithRel::AbsBounded)
            );
            assert_eq!(
                IntervalType::Bounded.try_with_rel(Relativity::Relative),
                Ok(IntervalTypeWithRel::RelBounded)
            );
            assert_eq!(
                IntervalType::Bounded.try_with_rel(Relativity::Any),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
        }

        #[test]
        fn half_bounded() {
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToFuture).try_with_rel(Relativity::Absolute),
                Ok(IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToPast).try_with_rel(Relativity::Absolute),
                Ok(IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToFuture).try_with_rel(Relativity::Relative),
                Ok(IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToPast).try_with_rel(Relativity::Relative),
                Ok(IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToFuture).try_with_rel(Relativity::Any),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToPast).try_with_rel(Relativity::Any),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
        }

        #[test]
        fn unbounded() {
            assert_eq!(
                IntervalType::Unbounded.try_with_rel(Relativity::Absolute),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalType::Unbounded.try_with_rel(Relativity::Relative),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalType::Unbounded.try_with_rel(Relativity::Any),
                Ok(IntervalTypeWithRel::Unbounded)
            );
        }

        #[test]
        fn empty() {
            assert_eq!(
                IntervalType::Empty.try_with_rel(Relativity::Absolute),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalType::Empty.try_with_rel(Relativity::Relative),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalType::Empty.try_with_rel(Relativity::Any),
                Ok(IntervalTypeWithRel::Empty)
            );
        }
    }

    #[test]
    fn is_empty() {
        assert!(!IntervalType::Bounded.is_empty());
        assert!(!IntervalType::HalfBounded(OpeningDirection::ToFuture).is_empty());
        assert!(!IntervalType::HalfBounded(OpeningDirection::ToPast).is_empty());
        assert!(!IntervalType::Unbounded.is_empty());
        assert!(IntervalType::Empty.is_empty());
    }

    #[test]
    fn openness() {
        assert_eq!(IntervalType::Bounded.openness(), Openness::Bounded);
        assert_eq!(
            IntervalType::HalfBounded(OpeningDirection::ToFuture).openness(),
            Openness::HalfBounded
        );
        assert_eq!(
            IntervalType::HalfBounded(OpeningDirection::ToPast).openness(),
            Openness::HalfBounded
        );
        assert_eq!(IntervalType::Unbounded.openness(), Openness::Unbounded);
        assert_eq!(IntervalType::Empty.openness(), Openness::Empty);
    }

    #[test]
    fn from_interval_type_with_rel() {
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::AbsBounded),
            IntervalType::Bounded
        );
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::RelBounded),
            IntervalType::Bounded
        );
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture)),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast)),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture)),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast)),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
        assert_eq!(
            IntervalType::from(IntervalTypeWithRel::Unbounded),
            IntervalType::Unbounded
        );
        assert_eq!(IntervalType::from(IntervalTypeWithRel::Empty), IntervalType::Empty);
    }
}

mod interval_type_with_rel {
    use super::*;

    #[test]
    fn is_empty() {
        assert!(!IntervalTypeWithRel::AbsBounded.is_empty());
        assert!(!IntervalTypeWithRel::RelBounded.is_empty());
        assert!(!IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture).is_empty());
        assert!(!IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast).is_empty());
        assert!(!IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture).is_empty());
        assert!(!IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast).is_empty());
        assert!(!IntervalTypeWithRel::Unbounded.is_empty());
        assert!(IntervalTypeWithRel::Empty.is_empty());
    }

    #[test]
    fn relativity() {
        assert_eq!(IntervalTypeWithRel::AbsBounded.relativity(), Relativity::Absolute);
        assert_eq!(IntervalTypeWithRel::RelBounded.relativity(), Relativity::Relative);
        assert_eq!(
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture).relativity(),
            Relativity::Absolute
        );
        assert_eq!(
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast).relativity(),
            Relativity::Absolute
        );
        assert_eq!(
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture).relativity(),
            Relativity::Relative
        );
        assert_eq!(
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast).relativity(),
            Relativity::Relative
        );
        assert_eq!(IntervalTypeWithRel::Unbounded.relativity(), Relativity::Any);
        assert_eq!(IntervalTypeWithRel::Empty.relativity(), Relativity::Any);
    }

    #[test]
    fn openness() {
        assert_eq!(IntervalTypeWithRel::AbsBounded.openness(), Openness::Bounded);
        assert_eq!(IntervalTypeWithRel::RelBounded.openness(), Openness::Bounded);
        assert_eq!(
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture).openness(),
            Openness::HalfBounded
        );
        assert_eq!(
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast).openness(),
            Openness::HalfBounded
        );
        assert_eq!(
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture).openness(),
            Openness::HalfBounded
        );
        assert_eq!(
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast).openness(),
            Openness::HalfBounded
        );
        assert_eq!(IntervalTypeWithRel::Unbounded.openness(), Openness::Unbounded);
        assert_eq!(IntervalTypeWithRel::Empty.openness(), Openness::Empty);
    }

    #[test]
    fn has_interval_type() {
        assert_eq!(IntervalTypeWithRel::AbsBounded.interval_type(), IntervalType::Bounded);
        assert_eq!(IntervalTypeWithRel::RelBounded.interval_type(), IntervalType::Bounded);
        assert_eq!(
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture).interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
        assert_eq!(
            IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast).interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
        assert_eq!(
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture).interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToFuture)
        );
        assert_eq!(
            IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast).interval_type(),
            IntervalType::HalfBounded(OpeningDirection::ToPast)
        );
        assert_eq!(IntervalTypeWithRel::Unbounded.interval_type(), IntervalType::Unbounded);
        assert_eq!(IntervalTypeWithRel::Empty.interval_type(), IntervalType::Empty);
    }

    mod try_from_interval_type_and_relativity {
        use super::*;

        #[test]
        fn bounded() {
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Bounded, Relativity::Absolute)),
                Ok(IntervalTypeWithRel::AbsBounded)
            );
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Bounded, Relativity::Relative)),
                Ok(IntervalTypeWithRel::RelBounded)
            );
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Bounded, Relativity::Any)),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
        }

        #[test]
        fn half_bounded() {
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToFuture).try_with_rel(Relativity::Absolute),
                Ok(IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToFuture))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToPast).try_with_rel(Relativity::Absolute),
                Ok(IntervalTypeWithRel::AbsHalfBounded(OpeningDirection::ToPast))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToFuture).try_with_rel(Relativity::Relative),
                Ok(IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToFuture))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToPast).try_with_rel(Relativity::Relative),
                Ok(IntervalTypeWithRel::RelHalfBounded(OpeningDirection::ToPast))
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToFuture).try_with_rel(Relativity::Any),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalType::HalfBounded(OpeningDirection::ToPast).try_with_rel(Relativity::Any),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
        }

        #[test]
        fn unbounded() {
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Unbounded, Relativity::Absolute)),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Unbounded, Relativity::Relative)),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Unbounded, Relativity::Any)),
                Ok(IntervalTypeWithRel::Unbounded)
            );
        }

        #[test]
        fn empty() {
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Empty, Relativity::Absolute)),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Empty, Relativity::Relative)),
                Err(IntervalTypeWithRelTryFromIntervalTypeAndRel)
            );
            assert_eq!(
                IntervalTypeWithRel::try_from((IntervalType::Empty, Relativity::Any)),
                Ok(IntervalTypeWithRel::Empty)
            );
        }
    }
}

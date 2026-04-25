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

use std::ops::Bound;
use std::time::Duration;

use jiff::SignedDuration;

use super::bounded_interval::*;
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
use crate::intervals::relative::{
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn unchecked_new() {
    let interval = BoundedRelativeInterval::unchecked_new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(interval.start(), SignedDuration::from_hours(1));
    assert_eq!(interval.end(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod new {
    use super::*;

    #[test]
    fn no_swap() {
        let interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn swap() {
        let interval = BoundedRelativeInterval::new(SignedDuration::from_hours(2), SignedDuration::from_hours(1));

        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod new_with_length {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            BoundedRelativeInterval::new_with_length(SignedDuration::from_hours(1), Duration::from_hours(5)),
            Ok(BoundedRelativeInterval::new(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(6)
            ))
        );
    }

    #[test]
    fn out_of_range_length() {
        assert_eq!(
            BoundedRelativeInterval::new_with_length(SignedDuration::from_hours(1), Duration::MAX),
            Err(BoundedRelativeIntervalCreationError::OutOfRangeEnd)
        );
    }
}

#[test]
fn unchecked_new_with_inclusivity() {
    let interval = BoundedRelativeInterval::unchecked_new_with_inclusivity(
        SignedDuration::from_hours(2),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(1),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start(), SignedDuration::from_hours(2));
    assert_eq!(interval.end(), SignedDuration::from_hours(1));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod new_with_inclusivity {
    use super::*;

    #[test]
    fn no_swap() {
        let interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn swap() {
        let interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod new_with_length_and_inclusivity {
    use super::*;

    #[test]
    fn normal() {
        assert_eq!(
            BoundedRelativeInterval::new_with_length_and_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                Duration::from_hours(5),
                BoundInclusivity::Exclusive
            ),
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                SignedDuration::from_hours(6),
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn zero_length() {
        assert_eq!(
            BoundedRelativeInterval::new_with_length_and_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                Duration::ZERO,
                BoundInclusivity::Exclusive,
            ),
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive
            ))
        );
    }

    #[test]
    fn out_of_range_length() {
        assert_eq!(
            BoundedRelativeInterval::new_with_length_and_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                Duration::MAX,
                BoundInclusivity::Exclusive
            ),
            Err(BoundedRelativeIntervalCreationError::OutOfRangeEnd)
        );
    }
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from_range(start..=end),
            Ok(BoundedRelativeInterval::new(start, end))
        );
    }

    #[test]
    fn included_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from_range(start..end),
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Inclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn included_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            BoundedRelativeInterval::try_from_range(start..),
            Err(BoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Inclusive
            ))
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            BoundedRelativeInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Err(BoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_included() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from_range(..=end),
            Err(BoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from_range(..end),
            Err(BoundedRelativeIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            BoundedRelativeInterval::try_from_range(..),
            Err(BoundedRelativeIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).start(),
        SignedDuration::from_hours(1)
    );
}

#[test]
fn end() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).end(),
        SignedDuration::from_hours(2),
    );
}

#[test]
fn start_inclusivity() {
    assert_eq!(
        BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        )
        .start_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn end_inclusivity() {
    assert_eq!(
        BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        )
        .end_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn unchecked_set_start() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(2),
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_start(SignedDuration::from_hours(3));

    assert_eq!(interval.start(), SignedDuration::from_hours(3));
    assert_eq!(interval.end(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn unchecked_set_end() {
    let mut interval = BoundedRelativeInterval::new_with_inclusivity(
        SignedDuration::from_hours(2),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(3),
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_end(SignedDuration::from_hours(1));

    assert_eq!(interval.start(), SignedDuration::from_hours(2));
    assert_eq!(interval.end(), SignedDuration::from_hours(1));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod set_start {
    use super::*;

    #[test]
    fn set_start_less() {
        let new_start = SignedDuration::from_hours(1);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(2), SignedDuration::from_hours(3));

        assert_eq!(interval.set_start(new_start), Ok(()));
        assert_eq!(interval.start(), new_start);
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive_by_moving_start_incl() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn set_start_equal_makes_doubly_inclusive() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_start(new_start), Ok(()));
        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_start_greater_middle() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(3));

        assert_eq!(interval.set_start(new_start), Ok(()));
        assert_eq!(interval.start(), new_start);
    }

    #[test]
    fn set_start_greater_after() {
        let new_start = SignedDuration::from_hours(3);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
    }
}

mod set_end {
    use super::*;

    #[test]
    fn set_end_less_before() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(2), SignedDuration::from_hours(3));

        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.end(), SignedDuration::from_hours(3));
    }

    #[test]
    fn set_end_less_middle() {
        let new_end = SignedDuration::from_hours(2);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(3));

        assert_eq!(interval.set_end(new_end), Ok(()));
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end(), SignedDuration::from_hours(2));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive_by_moving_end_incl() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end(), SignedDuration::from_hours(2));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn set_end_equal_makes_doubly_inclusive() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_end(new_end), Ok(()));
        assert_eq!(interval.end(), new_end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_end_greater() {
        let new_start = SignedDuration::from_hours(3);

        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelativeIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
    }
}

mod set_length_from_start {
    use super::*;

    #[test]
    fn zero_length() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_start(Duration::ZERO), Ok(()));
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(1));
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let mut interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(6),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_length_from_start(Duration::ZERO),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(6));
    }

    #[test]
    fn normal_length() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_start(Duration::from_hours(2)), Ok(()));
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(3));
    }

    #[test]
    fn out_of_range_length() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(
            interval.set_length_from_start(Duration::MAX),
            Err(BoundedRelativeIntervalUpdateError::OutOfRange)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(6));
    }
}

mod set_length_from_end {
    use super::*;

    #[test]
    fn zero_length() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_end(Duration::ZERO), Ok(()));
        assert_eq!(interval.start(), SignedDuration::from_hours(6));
        assert_eq!(interval.end(), SignedDuration::from_hours(6));
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let mut interval = BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(6),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_length_from_end(Duration::ZERO),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(6));
    }

    #[test]
    fn normal_length() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_end(Duration::from_hours(2)), Ok(()));
        assert_eq!(interval.start(), SignedDuration::from_hours(4));
        assert_eq!(interval.end(), SignedDuration::from_hours(6));
    }

    #[test]
    fn out_of_range_length() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(
            interval.set_length_from_end(Duration::MAX),
            Err(BoundedRelativeIntervalUpdateError::OutOfRange)
        );
        assert_eq!(interval.start(), SignedDuration::from_hours(1));
        assert_eq!(interval.end(), SignedDuration::from_hours(6));
    }
}

#[test]
fn unchecked_set_start_inclusivity() {
    let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

    interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start(), interval.end());
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn unchecked_set_end_inclusivity() {
    let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

    interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start(), interval.end());
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

mod set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_start_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn breaks_doubly_inclusive() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

        assert_eq!(
            interval.set_start_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_end_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn breaks_doubly_inclusive() {
        let mut interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

        assert_eq!(
            interval.set_end_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedRelativeIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

#[test]
fn to_interval() {
    let interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(interval.clone().to_interval(), RelativeInterval::Bounded(interval));
}

#[test]
fn to_emptiable_interval() {
    let interval = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(
        interval.clone().to_emptiable_interval(),
        EmptiableRelativeInterval::Bound(RelativeInterval::Bounded(interval))
    );
}

#[test]
fn openness() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).openness(),
        Openness::Bounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).relativity(),
        Relativity::Relative
    );
}

#[test]
fn duration() {
    assert_eq!(
        BoundedRelativeInterval::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        )
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(1), Epsilon::Start)
    );
}

#[test]
fn rel_bound_pair() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).rel_bound_pair(),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
        )
    );
}

#[test]
fn rel_start() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).rel_start(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound()
    );
}

#[test]
fn rel_end() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2),).rel_end(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
    );
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2),)
            .emptiable_rel_bound_pair(),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
    );
}

#[test]
fn partial_rel_start() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2),).partial_rel_start(),
        Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound())
    );
}

#[test]
fn partial_rel_end() {
    assert_eq!(
        BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2),).partial_rel_end(),
        Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(!BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2),).is_empty());
}

#[test]
fn from_timestamp_pair() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(2);

    assert_eq!(
        BoundedRelativeInterval::from((start, end)),
        BoundedRelativeInterval::new(start, end)
    );
}

#[test]
fn from_timestamp_incl_pair() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(2);

    assert_eq!(
        BoundedRelativeInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive))),
        BoundedRelativeInterval::new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive
        )
    );
}

#[test]
fn from_range_included_excluded() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(2);

    assert_eq!(
        BoundedRelativeInterval::from(start..end),
        BoundedRelativeInterval::new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive
        )
    );
}

#[test]
fn from_range_included_included() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(1);

    assert_eq!(
        BoundedRelativeInterval::from(start..=end),
        BoundedRelativeInterval::new_with_inclusivity(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Inclusive
        ),
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(start).to_start_bound(),
                RelativeFiniteBoundPosition::new(end).to_end_bound()
            )),
            Ok(BoundedRelativeInterval::new(start, end))
        );
    }

    #[test]
    fn finite_infinite() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            BoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(start).to_start_bound(),
                RelativeEndBound::InfiniteFuture
            )),
            Err(BoundedRelativeIntervalTryFromRelativeBoundPairError)
        );
    }

    #[test]
    fn infinite_finite() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(end).to_end_bound()
            )),
            Err(BoundedRelativeIntervalTryFromRelativeBoundPairError)
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            BoundedRelativeInterval::try_from(RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::InfiniteFuture
            )),
            Err(BoundedRelativeIntervalTryFromRelativeBoundPairError)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_finite_finite() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from(
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(start).to_start_bound(),
                    RelativeFiniteBoundPosition::new(end).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(BoundedRelativeInterval::new(start, end))
        );
    }

    #[test]
    fn bound_finite_infinite() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            BoundedRelativeInterval::try_from(
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(start).to_start_bound(),
                    RelativeEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError)
        );
    }

    #[test]
    fn bound_infinite_finite() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelativeInterval::try_from(
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(end).to_end_bound()
                )
                .to_emptiable()
            ),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError)
        );
    }

    #[test]
    fn bound_infinite_infinite() {
        assert_eq!(
            BoundedRelativeInterval::try_from(
                RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedRelativeInterval::try_from(EmptiableRelativeBoundPair::Empty),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            BoundedRelativeInterval::try_from(bounded.clone().to_interval()),
            Ok(bounded)
        );
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            BoundedRelativeInterval::try_from(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
                    .to_interval()
            ),
            Err(BoundedRelativeIntervalFromRelativeIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            BoundedRelativeInterval::try_from(UnboundedInterval.to_rel_interval()),
            Err(BoundedRelativeIntervalFromRelativeIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() {
        let bounded = BoundedRelativeInterval::new(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            BoundedRelativeInterval::try_from(bounded.clone().to_emptiable_interval()),
            Ok(bounded)
        );
    }

    #[test]
    fn bound_half_bounded() {
        assert_eq!(
            BoundedRelativeInterval::try_from(
                HalfBoundedRelativeInterval::new(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
                    .to_emptiable_interval()
            ),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            BoundedRelativeInterval::try_from(UnboundedInterval.to_emptiable_rel_interval()),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedRelativeInterval::try_from(EmptiableRelativeInterval::Empty(EmptyInterval)),
            Err(BoundedRelativeIntervalTryFromEmptiableRelativeIntervalError)
        );
    }
}

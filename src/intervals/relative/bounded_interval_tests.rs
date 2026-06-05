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
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn unchecked_new() {
    let interval =
        BoundedRelInterval::unchecked_from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
    assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod new {
    use super::*;

    #[test]
    fn no_swap() {
        let interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn swap() {
        let interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(2), SignedDuration::from_hours(1));

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod new_with_length {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            BoundedRelInterval::from_start_len(SignedDuration::from_hours(1), Duration::from_hours(5)),
            Ok(BoundedRelInterval::from_offsets(
                SignedDuration::from_hours(1),
                SignedDuration::from_hours(6)
            ))
        );
    }

    #[test]
    fn out_of_range_length() {
        assert_eq!(
            BoundedRelInterval::from_start_len(SignedDuration::from_hours(1), Duration::MAX),
            Err(BoundedRelIntervalCreationError::OutOfRangeEnd)
        );
    }
}

#[test]
fn unchecked_new_with_inclusivity() {
    let interval = BoundedRelInterval::unchecked_from_offsets_incl(
        SignedDuration::from_hours(2),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(1),
        BoundInclusivity::Inclusive,
    );

    assert_eq!(interval.start_offset(), SignedDuration::from_hours(2));
    assert_eq!(interval.end_offset(), SignedDuration::from_hours(1));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod new_with_inclusivity {
    use super::*;

    #[test]
    fn no_swap() {
        let interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn swap() {
        let interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod new_with_length_and_inclusivity {
    use super::*;

    #[test]
    fn normal() {
        assert_eq!(
            BoundedRelInterval::from_start_len_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                Duration::from_hours(5),
                BoundInclusivity::Exclusive
            ),
            Ok(BoundedRelInterval::from_offsets_incl(
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
            BoundedRelInterval::from_start_len_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                Duration::ZERO,
                BoundInclusivity::Exclusive,
            ),
            Ok(BoundedRelInterval::from_offsets_incl(
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
            BoundedRelInterval::from_start_len_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
                Duration::MAX,
                BoundInclusivity::Exclusive
            ),
            Err(BoundedRelIntervalCreationError::OutOfRangeEnd)
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
            BoundedRelInterval::try_from_range(start..=end),
            Ok(BoundedRelInterval::from_offsets(start, end))
        );
    }

    #[test]
    fn included_excluded() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from_range(start..end),
            Ok(BoundedRelInterval::from_offsets_incl(
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
            BoundedRelInterval::try_from_range(start..),
            Err(BoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_included() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Ok(BoundedRelInterval::from_offsets_incl(
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
            BoundedRelInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Ok(BoundedRelInterval::from_offsets_incl(
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
            BoundedRelInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Err(BoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_included() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from_range(..=end),
            Err(BoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from_range(..end),
            Err(BoundedRelIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            BoundedRelInterval::try_from_range(..),
            Err(BoundedRelIntervalTryFromRangeError)
        );
    }
}

#[test]
fn start() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).start_offset(),
        SignedDuration::from_hours(1)
    );
}

#[test]
fn end() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).end_offset(),
        SignedDuration::from_hours(2),
    );
}

#[test]
fn start_inclusivity() {
    assert_eq!(
        BoundedRelInterval::from_offsets_incl(
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
        BoundedRelInterval::from_offsets_incl(
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
    let mut interval = BoundedRelInterval::from_offsets_incl(
        SignedDuration::from_hours(1),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(2),
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_start_offset(SignedDuration::from_hours(3));

    assert_eq!(interval.start_offset(), SignedDuration::from_hours(3));
    assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn unchecked_set_end() {
    let mut interval = BoundedRelInterval::from_offsets_incl(
        SignedDuration::from_hours(2),
        BoundInclusivity::Exclusive,
        SignedDuration::from_hours(3),
        BoundInclusivity::Inclusive,
    );

    interval.unchecked_set_end_offset(SignedDuration::from_hours(1));

    assert_eq!(interval.start_offset(), SignedDuration::from_hours(2));
    assert_eq!(interval.end_offset(), SignedDuration::from_hours(1));
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

mod set_start {
    use super::*;

    #[test]
    fn set_start_less() {
        let new_start = SignedDuration::from_hours(1);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(2), SignedDuration::from_hours(3));

        assert_eq!(interval.set_start_offset(new_start), Ok(()));
        assert_eq!(interval.start_offset(), new_start);
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_start_offset(new_start),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_start_equal_breaks_doubly_inclusive_by_moving_start_incl() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_start_offset(new_start),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn set_start_equal_makes_doubly_inclusive() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_start_offset(new_start), Ok(()));
        assert_eq!(interval.start_offset(), new_start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_start_greater_middle() {
        let new_start = SignedDuration::from_hours(2);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(3));

        assert_eq!(interval.set_start_offset(new_start), Ok(()));
        assert_eq!(interval.start_offset(), new_start);
    }

    #[test]
    fn set_start_greater_after() {
        let new_start = SignedDuration::from_hours(3);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            interval.set_start_offset(new_start),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
    }
}

mod set_end {
    use super::*;

    #[test]
    fn set_end_less_before() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(2), SignedDuration::from_hours(3));

        assert_eq!(
            interval.set_end_offset(new_end),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(3));
    }

    #[test]
    fn set_end_less_middle() {
        let new_end = SignedDuration::from_hours(2);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(3));

        assert_eq!(interval.set_end_offset(new_end), Ok(()));
        assert_eq!(interval.end_offset(), new_end);
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Inclusive,
        );

        assert_eq!(
            interval.set_end_offset(new_end),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_end_equal_breaks_doubly_inclusive_by_moving_end_incl() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(2),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_end_offset(new_end),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn set_end_equal_makes_doubly_inclusive() {
        let new_end = SignedDuration::from_hours(1);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_end_offset(new_end), Ok(()));
        assert_eq!(interval.end_offset(), new_end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_end_greater() {
        let new_start = SignedDuration::from_hours(3);

        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            interval.set_start_offset(new_start),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
    }
}

mod set_length_from_start {
    use super::*;

    #[test]
    fn zero_length() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_start(Duration::ZERO), Ok(()));
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(1));
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let mut interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(6),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_length_from_start(Duration::ZERO),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(6));
    }

    #[test]
    fn normal_length() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_start(Duration::from_hours(2)), Ok(()));
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(3));
    }

    #[test]
    fn out_of_range_length() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(
            interval.set_length_from_start(Duration::MAX),
            Err(BoundedRelIntervalUpdateError::OutOfRange)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(6));
    }
}

mod set_length_from_end {
    use super::*;

    #[test]
    fn zero_length() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_end(Duration::ZERO), Ok(()));
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(6));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(6));
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let mut interval = BoundedRelInterval::from_offsets_incl(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
            SignedDuration::from_hours(6),
            BoundInclusivity::Exclusive,
        );

        assert_eq!(
            interval.set_length_from_end(Duration::ZERO),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(6));
    }

    #[test]
    fn normal_length() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(interval.set_length_from_end(Duration::from_hours(2)), Ok(()));
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(4));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(6));
    }

    #[test]
    fn out_of_range_length() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(6));

        assert_eq!(
            interval.set_length_from_end(Duration::MAX),
            Err(BoundedRelIntervalUpdateError::OutOfRange)
        );
        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(6));
    }
}

#[test]
fn unchecked_set_start_inclusivity() {
    let mut interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

    interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start_offset(), interval.end_offset());
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
}

#[test]
fn unchecked_set_end_inclusivity() {
    let mut interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

    interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

    assert_eq!(interval.start_offset(), interval.end_offset());
    assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
}

mod set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_start_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn breaks_doubly_inclusive() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

        assert_eq!(
            interval.set_start_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(interval.set_end_inclusivity(BoundInclusivity::Exclusive), Ok(()));
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn breaks_doubly_inclusive() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));

        assert_eq!(
            interval.set_end_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

#[test]
fn to_interval() {
    let interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(interval.clone().to_interval(), RelInterval::Bounded(interval));
}

#[test]
fn to_emptiable_interval() {
    let interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

    assert_eq!(
        interval.clone().to_emptiable_interval(),
        EmptiableRelInterval::Bound(RelInterval::Bounded(interval))
    );
}

#[test]
fn openness() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).openness(),
        Openness::Bounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).relativity(),
        Relativity::Rel
    );
}

#[test]
fn duration() {
    assert_eq!(
        BoundedRelInterval::from_offsets_incl(
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
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).rel_bound_pair(),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
        )
    );
}

#[test]
fn rel_start() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2)).rel_start(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
    );
}

#[test]
fn rel_end() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),).rel_end(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
    );
}

#[test]
fn emptiable_rel_bound_pair() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),)
            .emptiable_rel_bound_pair(),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
        )
        .to_emptiable()
    );
}

#[test]
fn partial_rel_start() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),)
            .partial_rel_start(),
        Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound())
    );
}

#[test]
fn partial_rel_end() {
    assert_eq!(
        BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),)
            .partial_rel_end(),
        Some(RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(
        !BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2),).is_empty()
    );
}

#[test]
fn from_timestamp_pair() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(2);

    assert_eq!(
        BoundedRelInterval::from((start, end)),
        BoundedRelInterval::from_offsets(start, end)
    );
}

#[test]
fn from_timestamp_incl_pair() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(2);

    assert_eq!(
        BoundedRelInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive))),
        BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive)
    );
}

#[test]
fn from_range_included_excluded() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(2);

    assert_eq!(
        BoundedRelInterval::from(start..end),
        BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive)
    );
}

#[test]
fn from_range_included_included() {
    let start = SignedDuration::from_hours(1);
    let end = SignedDuration::from_hours(1);

    assert_eq!(
        BoundedRelInterval::from(start..=end),
        BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Inclusive),
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from(RelBoundPair::new(
                RelFiniteBoundPos::new(start).to_start_bound(),
                RelFiniteBoundPos::new(end).to_end_bound()
            )),
            Ok(BoundedRelInterval::from_offsets(start, end))
        );
    }

    #[test]
    fn finite_infinite() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            BoundedRelInterval::try_from(RelBoundPair::new(
                RelFiniteBoundPos::new(start).to_start_bound(),
                RelEndBound::InfiniteFuture
            )),
            Err(BoundedRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn infinite_finite() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(end).to_end_bound()
            )),
            Err(BoundedRelIntervalTryFromRelBoundPairError)
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            BoundedRelInterval::try_from(RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelEndBound::InfiniteFuture
            )),
            Err(BoundedRelIntervalTryFromRelBoundPairError)
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
            BoundedRelInterval::try_from(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(start).to_start_bound(),
                    RelFiniteBoundPos::new(end).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(BoundedRelInterval::from_offsets(start, end))
        );
    }

    #[test]
    fn bound_finite_infinite() {
        let start = SignedDuration::from_hours(1);

        assert_eq!(
            BoundedRelInterval::try_from(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(start).to_start_bound(),
                    RelEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Err(BoundedRelIntervalTryFromEmptiableRelBoundPairError)
        );
    }

    #[test]
    fn bound_infinite_finite() {
        let end = SignedDuration::from_hours(2);

        assert_eq!(
            BoundedRelInterval::try_from(
                RelBoundPair::new(RelStartBound::InfinitePast, RelFiniteBoundPos::new(end).to_end_bound())
                    .to_emptiable()
            ),
            Err(BoundedRelIntervalTryFromEmptiableRelBoundPairError)
        );
    }

    #[test]
    fn bound_infinite_infinite() {
        assert_eq!(
            BoundedRelInterval::try_from(
                RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture).to_emptiable()
            ),
            Err(BoundedRelIntervalTryFromEmptiableRelBoundPairError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedRelInterval::try_from(EmptiableRelBoundPair::Empty),
            Err(BoundedRelIntervalTryFromEmptiableRelBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() {
        let bounded = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(BoundedRelInterval::try_from(bounded.clone().to_interval()), Ok(bounded));
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            BoundedRelInterval::try_from(
                HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
                    .to_interval()
            ),
            Err(BoundedRelIntervalFromRelIntervalError)
        );
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            BoundedRelInterval::try_from(UnboundedInterval.to_rel_interval()),
            Err(BoundedRelIntervalFromRelIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() {
        let bounded = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));

        assert_eq!(
            BoundedRelInterval::try_from(bounded.clone().to_emptiable_interval()),
            Ok(bounded)
        );
    }

    #[test]
    fn bound_half_bounded() {
        assert_eq!(
            BoundedRelInterval::try_from(
                HalfBoundedRelInterval::from_offset(SignedDuration::from_hours(1), OpeningDirection::ToFuture)
                    .to_emptiable_interval()
            ),
            Err(BoundedRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            BoundedRelInterval::try_from(UnboundedInterval.to_emptiable_rel_interval()),
            Err(BoundedRelIntervalTryFromEmptiableRelIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            BoundedRelInterval::try_from(EmptiableRelInterval::Empty(EmptyInterval)),
            Err(BoundedRelIntervalTryFromEmptiableRelIntervalError)
        );
    }
}

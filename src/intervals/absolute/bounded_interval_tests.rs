use std::ops::Bound;
use std::time::Duration;

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
    HasIntervalType,
    HasIntervalTypeWithRel,
    HasOpenness,
    HasRelativity,
    IntervalType,
    IntervalTypeWithRel,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::test_utils::{date_timestamp, datetime_timestamp};

mod unchecked_new {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
        let interval = BoundedAbsInterval::unchecked_new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        let interval = BoundedAbsInterval::unchecked_new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
            .to_finite_start_bound();
        let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let interval = BoundedAbsInterval::unchecked_new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }
}

mod new {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
        let interval = BoundedAbsInterval::new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start_pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2));
        let end_pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        let interval = BoundedAbsInterval::new(start_pos.to_finite_start_bound(), end_pos.to_finite_end_bound());

        assert_eq!(interval.start(), end_pos.to_finite_start_bound());
        assert_eq!(interval.end(), start_pos.to_finite_end_bound());
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let interval = BoundedAbsInterval::new(start, end);

        assert_eq!(
            interval.start(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
        );
        assert_eq!(
            interval.end(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
        );
    }
}

mod unchecked_from_times {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::unchecked_from_times(start, end);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_times(start, end);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
    }
}

mod from_times {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::from_times(start, end);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_times(start, end);

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), start);
    }
}

mod unchecked_from_times_incl {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::unchecked_from_times_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_times_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_times_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod from_times_incl {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 1);
        let interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 1);
        let interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod from_start_len {
    use super::*;

    #[test]
    fn zero_length() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_start_len(start, Duration::ZERO).unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_start_len(start, Duration::from_hours(1)).unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), datetime_timestamp(2026, 1, 1, 1, 0, 0));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod unchecked_from_start_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn some_length() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), datetime_timestamp(2026, 1, 1, 1, 0, 0));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod from_start_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let start = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), datetime_timestamp(2026, 1, 1, 1, 0, 0));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod from_end_len {
    use super::*;

    #[test]
    fn zero_length() {
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_end_len(end, Duration::ZERO).unwrap();

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::from_end_len(end, Duration::from_hours(1)).unwrap();

        assert_eq!(interval.start_time(), datetime_timestamp(2026, 1, 1, 23, 0, 0));
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod unchecked_from_end_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::unchecked_from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::unchecked_from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), datetime_timestamp(2026, 1, 1, 23, 0, 0));
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod from_end_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_time(), datetime_timestamp(2026, 1, 1, 23, 0, 0));
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from_range(start..=end),
            Ok(BoundedAbsInterval::from_times(start, end))
        );
    }

    #[test]
    fn included_excluded() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from_range(start..end),
            Ok(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Inclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn included_unbounded() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            BoundedAbsInterval::try_from_range(start..),
            Err(BoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn excluded_included() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Ok(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Inclusive
            ))
        );
    }

    #[test]
    fn excluded_excluded() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Ok(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
    }

    #[test]
    fn excluded_unbounded() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            BoundedAbsInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Err(BoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_included() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from_range(..=end),
            Err(BoundedAbsIntervalTryFromRangeError)
        );
    }

    #[test]
    fn unbounded_excluded() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from_range(..end),
            Err(BoundedAbsIntervalTryFromRangeError)
        );
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
fn start() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
    assert_eq!(BoundedAbsInterval::new(start, end).start(), start);
}

#[test]
fn end() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
    assert_eq!(BoundedAbsInterval::new(start, end).end(), end);
}

#[test]
fn start_time() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
    assert_eq!(
        BoundedAbsInterval::new(start, end).start_time(),
        date_timestamp(2026, 1, 1)
    );
}

#[test]
fn end_time() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
    assert_eq!(
        BoundedAbsInterval::new(start, end).end_time(),
        date_timestamp(2026, 1, 2)
    );
}

#[test]
fn start_inclusivity() {
    let start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
        .to_finite_start_bound();
    let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
    assert_eq!(
        BoundedAbsInterval::new(start, end).start_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn end_inclusivity() {
    let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    let end =
        AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive).to_finite_end_bound();
    assert_eq!(
        BoundedAbsInterval::new(start, end).end_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

mod unchecked_set_start {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }
}

mod set_start {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        assert_eq!(interval.set_start(new_start), Ok(()));

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_finite_start_bound();
        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_end {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }
}

mod set_end {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_finite_end_bound();
        assert_eq!(interval.set_end(new_end), Ok(()));

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
        let mut interval = BoundedAbsInterval::new(start, end);

        let new_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_start_time {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_start = date_timestamp(2026, 1, 1);
        interval.unchecked_set_start_time(new_start);

        assert_eq!(interval.start_time(), new_start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_start = date_timestamp(2026, 1, 4);
        interval.unchecked_set_start_time(new_start);

        assert_eq!(interval.start_time(), new_start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_start = date_timestamp(2026, 1, 2);
        interval.unchecked_set_start_time(new_start);

        assert_eq!(interval.start_time(), new_start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod set_start_time {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_start = date_timestamp(2026, 1, 1);
        assert_eq!(interval.set_start_time(new_start), Ok(()));

        assert_eq!(interval.start_time(), new_start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn ok_same_pos() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_start = end;
        assert_eq!(interval.set_start_time(new_start), Ok(()));

        assert_eq!(interval.start_time(), new_start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_start = date_timestamp(2026, 1, 4);
        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_start = date_timestamp(2026, 1, 2);
        assert_eq!(
            interval.set_start_time(new_start),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_end_time {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_end = date_timestamp(2026, 1, 4);
        interval.unchecked_set_end_time(new_end);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_end = date_timestamp(2026, 1, 1);
        interval.unchecked_set_end_time(new_end);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), new_end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_end = date_timestamp(2026, 1, 1);
        interval.unchecked_set_end_time(new_end);

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_time(), new_end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod set_end_time {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_end = date_timestamp(2026, 1, 4);
        assert_eq!(interval.set_end_time(new_end), Ok(()));

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), new_end);
    }

    #[test]
    fn ok_same_pos() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_end = start;
        assert_eq!(interval.set_end_time(new_end), Ok(()));

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 3);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        let new_end = date_timestamp(2026, 1, 1);
        assert_eq!(
            interval.set_end_time(new_end),
            Err(BoundedAbsIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_end = date_timestamp(2026, 1, 1);
        assert_eq!(
            interval.set_end_time(new_end),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod set_length_from_start {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        assert_eq!(interval.set_length_from_start(Duration::from_hours(1)), Ok(()));

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), datetime_timestamp(2026, 1, 1, 1, 0, 0));
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_incl_excl() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(
            interval.set_length_from_start(Duration::ZERO),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_excl_incl() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Exclusive, end, BoundInclusivity::Inclusive);

        assert_eq!(
            interval.set_length_from_start(Duration::ZERO),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod set_length_from_end {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval = BoundedAbsInterval::from_times(start, end);

        assert_eq!(interval.set_length_from_end(Duration::from_hours(1)), Ok(()));

        assert_eq!(interval.start_time(), datetime_timestamp(2026, 1, 1, 23, 0, 0));
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_incl_excl() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(
            interval.set_length_from_end(Duration::ZERO),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_excl_incl() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let mut interval =
            BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Exclusive, end, BoundInclusivity::Inclusive);

        assert_eq!(
            interval.set_length_from_end(Duration::ZERO),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
        interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 1));
        interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_time(), interval.end_time());
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
        assert_eq!(interval.set_start_inclusivity(BoundInclusivity::Exclusive), Ok(()));

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_start_inclusivity() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 1));
        assert_eq!(
            interval.set_start_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
        interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 1));
        interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_time(), interval.end_time());
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
        assert_eq!(interval.set_end_inclusivity(BoundInclusivity::Exclusive), Ok(()));

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn set_start_inclusivity() {
        let mut interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 1));
        assert_eq!(
            interval.set_end_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedAbsIntervalUpdateError::SameTimeDoublyInclusiveViolation)
        );
    }
}

#[test]
fn to_interval() {
    let interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));

    assert_eq!(interval.clone().to_interval(), AbsInterval::Bounded(interval));
}

#[test]
fn to_emptiable_interval() {
    let interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));

    assert_eq!(
        interval.clone().to_emptiable_interval(),
        EmptiableAbsInterval::Bound(AbsInterval::Bounded(interval))
    );
}

#[test]
fn openness() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2)).openness(),
        Openness::Bounded
    );
}

#[test]
fn relativity() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2)).relativity(),
        Relativity::Absolute
    );
}

#[test]
fn duration() {
    assert_eq!(
        BoundedAbsInterval::from_times_incl(
            date_timestamp(2026, 1, 1),
            BoundInclusivity::Exclusive,
            date_timestamp(2026, 1, 2),
            BoundInclusivity::Inclusive,
        )
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(24), Epsilon::Start)
    );
}

#[test]
fn abs_bound_pair() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2)).abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
        )
    );
}

#[test]
fn abs_start() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2)).abs_start(),
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
    );
}

#[test]
fn abs_end() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2),).abs_end(),
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
    );
}

#[test]
fn emptiable_abs_bound_pair() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2),)
            .emptiable_abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound()
        )
        .to_emptiable()
    );
}

#[test]
fn partial_abs_start() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2),).partial_abs_start(),
        Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound())
    );
}

#[test]
fn partial_abs_end() {
    assert_eq!(
        BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2),).partial_abs_end(),
        Some(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound())
    );
}

#[test]
fn is_empty() {
    assert!(!BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2),).is_empty());
}

#[test]
fn interval_type() {
    let interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
    assert_eq!(interval.interval_type(), IntervalType::Bounded);
}

#[test]
fn interval_type_with_rel() {
    let interval = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));
    assert_eq!(interval.interval_type_with_rel(), IntervalTypeWithRel::AbsBounded);
}

mod from_finite_start_end_bounds {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start_pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2));
        let end_pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        let interval = BoundedAbsInterval::from((start_pos.to_finite_start_bound(), end_pos.to_finite_end_bound()));

        assert_eq!(interval.start(), end_pos.to_finite_start_bound());
        assert_eq!(interval.end(), start_pos.to_finite_end_bound());
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(
            interval.start(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
        );
        assert_eq!(
            interval.end(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
        );
    }
}

mod from_timestamp_pair {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 1);
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), start);
    }
}

mod from_timestamp_incl_pair {
    use super::*;

    #[test]
    fn ok() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);
        let interval =
            BoundedAbsInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive)));

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn chronological_order_violation() {
        let start = date_timestamp(2026, 1, 2);
        let end = date_timestamp(2026, 1, 1);
        let interval =
            BoundedAbsInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive)));

        assert_eq!(interval.start_time(), end);
        assert_eq!(interval.end_time(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 1);
        let interval =
            BoundedAbsInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive)));

        assert_eq!(interval.start_time(), start);
        assert_eq!(interval.end_time(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod from_finite_bound_pos_pair {
    use super::*;

    #[test]
    fn ok() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2));
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(interval.start(), start.to_finite_start_bound());
        assert_eq!(interval.end(), end.to_finite_end_bound());
    }

    #[test]
    fn chronological_order_violation() {
        let start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2));
        let end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(interval.start(), end.to_finite_start_bound());
        assert_eq!(interval.end(), start.to_finite_end_bound());
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
        let end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive);
        let interval = BoundedAbsInterval::from((start, end));

        assert_eq!(
            interval.start(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
        );
        assert_eq!(
            interval.end(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
        );
    }
}

#[test]
fn from_range_included_excluded() {
    let start = date_timestamp(2026, 1, 1);
    let end = date_timestamp(2026, 1, 2);

    assert_eq!(
        BoundedAbsInterval::from(start..end),
        BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive)
    );
}

#[test]
fn from_range_included_included() {
    let start = date_timestamp(2026, 1, 1);
    let end = date_timestamp(2026, 1, 1);

    assert_eq!(
        BoundedAbsInterval::from(start..=end),
        BoundedAbsInterval::from_times_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Inclusive),
    );
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(start).to_start_bound(),
                AbsFiniteBoundPos::new(end).to_end_bound()
            )),
            Ok(BoundedAbsInterval::from_times(start, end))
        );
    }

    #[test]
    fn finite_infinite() {
        let start = date_timestamp(2026, 1, 1);

        assert_eq!(
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsFiniteBoundPos::new(start).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            Err(BoundedAbsIntervalTryFromAbsBoundPairError)
        );
    }

    #[test]
    fn infinite_finite() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(end).to_end_bound()
            )),
            Err(BoundedAbsIntervalTryFromAbsBoundPairError)
        );
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
    fn bound_finite_finite() {
        let start = date_timestamp(2026, 1, 1);
        let end = date_timestamp(2026, 1, 2);

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
    }

    #[test]
    fn bound_finite_infinite() {
        let start = date_timestamp(2026, 1, 1);

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
    }

    #[test]
    fn bound_infinite_finite() {
        let end = date_timestamp(2026, 1, 2);

        assert_eq!(
            BoundedAbsInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsFiniteBoundPos::new(end).to_end_bound())
                    .to_emptiable()
            ),
            Err(BoundedAbsIntervalTryFromEmptiableAbsBoundPairError)
        );
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
    fn bounded() {
        let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));

        assert_eq!(BoundedAbsInterval::try_from(bounded.clone().to_interval()), Ok(bounded));
    }

    #[test]
    fn half_bounded() {
        assert_eq!(
            BoundedAbsInterval::try_from(
                HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture).to_interval()
            ),
            Err(BoundedAbsIntervalFromAbsIntervalError)
        );
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
    fn bound_bounded() {
        let bounded = BoundedAbsInterval::from_times(date_timestamp(2026, 1, 1), date_timestamp(2026, 1, 2));

        assert_eq!(
            BoundedAbsInterval::try_from(bounded.clone().to_emptiable_interval()),
            Ok(bounded)
        );
    }

    #[test]
    fn bound_half_bounded() {
        assert_eq!(
            BoundedAbsInterval::try_from(
                HalfBoundedAbsInterval::from_time(date_timestamp(2026, 1, 1), OpeningDirection::ToFuture)
                    .to_emptiable_interval()
            ),
            Err(BoundedAbsIntervalTryFromEmptiableAbsIntervalError)
        );
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

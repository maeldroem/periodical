use std::ops::Bound;
use std::time::Duration;

use jiff::SignedDuration;

use super::bounded_interval::*;
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

mod unchecked_new {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
        let interval = BoundedRelInterval::unchecked_new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        let interval = BoundedRelInterval::unchecked_new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
            .to_finite_start_bound();
        let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let interval = BoundedRelInterval::unchecked_new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }
}

mod new {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
        let interval = BoundedRelInterval::new(start, end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(2));
        let end_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        let interval = BoundedRelInterval::new(start_pos.to_finite_start_bound(), end_pos.to_finite_end_bound());

        assert_eq!(interval.start(), end_pos.to_finite_start_bound());
        assert_eq!(interval.end(), start_pos.to_finite_end_bound());
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let interval = BoundedRelInterval::new(start, end);

        assert_eq!(
            interval.start(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
        );
        assert_eq!(
            interval.end(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
        );
    }
}

mod unchecked_from_offsets {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::unchecked_from_offsets(start, end);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_offsets(start, end);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
    }
}

mod from_offsets {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::from_offsets(start, end);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_offsets(start, end);

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), start);
    }
}

mod unchecked_from_offsets_incl {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::unchecked_from_offsets_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_offsets_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_offsets_incl(
            start,
            BoundInclusivity::Inclusive,
            end,
            BoundInclusivity::Exclusive,
        );

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod from_offsets_incl {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(1);
        let interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(1);
        let interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod from_start_len {
    use super::*;

    #[test]
    fn zero_length() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_start_len(start, Duration::ZERO).unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_start_len(start, Duration::from_hours(1)).unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod unchecked_from_start_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn some_length() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod from_start_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let start = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_start_len_incl(
            start,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod from_end_len {
    use super::*;

    #[test]
    fn zero_length() {
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_end_len(end, Duration::ZERO).unwrap();

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::from_end_len(end, Duration::from_hours(1)).unwrap();

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod unchecked_from_end_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::unchecked_from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::unchecked_from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod from_end_len_incl {
    use super::*;

    #[test]
    fn zero_length() {
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Inclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn zero_length_breaks_doubly_inclusive() {
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::ZERO,
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn some_length() {
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::from_end_len_incl(
            end,
            BoundInclusivity::Inclusive,
            Duration::from_hours(1),
            BoundInclusivity::Exclusive,
        )
        .unwrap();

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(1));
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
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
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
    assert_eq!(BoundedRelInterval::new(start, end).start(), start);
}

#[test]
fn end() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
    assert_eq!(BoundedRelInterval::new(start, end).end(), end);
}

#[test]
fn start_offset() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
    assert_eq!(
        BoundedRelInterval::new(start, end).start_offset(),
        SignedDuration::from_hours(1)
    );
}

#[test]
fn end_offset() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
    assert_eq!(
        BoundedRelInterval::new(start, end).end_offset(),
        SignedDuration::from_hours(2)
    );
}

#[test]
fn start_inclusivity() {
    let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
        .to_finite_start_bound();
    let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
    assert_eq!(
        BoundedRelInterval::new(start, end).start_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

#[test]
fn end_inclusivity() {
    let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
        .to_finite_end_bound();
    assert_eq!(
        BoundedRelInterval::new(start, end).end_inclusivity(),
        BoundInclusivity::Exclusive
    );
}

mod unchecked_set_start {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        interval.unchecked_set_start(new_start);

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }
}

mod set_start {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        assert_eq!(interval.set_start(new_start), Ok(()));

        assert_eq!(interval.start(), new_start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_finite_start_bound();
        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        assert_eq!(
            interval.set_start(new_start),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_end {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        interval.unchecked_set_end(new_end);

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }
}

mod set_end {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_finite_end_bound();
        assert_eq!(interval.set_end(new_end), Ok(()));

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_input() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_coming_from_state() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
        let mut interval = BoundedRelInterval::new(start, end);

        let new_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();
        assert_eq!(
            interval.set_end(new_end),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_start_offset {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_start = SignedDuration::from_hours(1);
        interval.unchecked_set_start_offset(new_start);

        assert_eq!(interval.start_offset(), new_start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_start = SignedDuration::from_hours(4);
        interval.unchecked_set_start_offset(new_start);

        assert_eq!(interval.start_offset(), new_start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_start = SignedDuration::from_hours(2);
        interval.unchecked_set_start_offset(new_start);

        assert_eq!(interval.start_offset(), new_start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod set_start_offset {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_start = SignedDuration::from_hours(1);
        assert_eq!(interval.set_start_offset(new_start), Ok(()));

        assert_eq!(interval.start_offset(), new_start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn ok_same_pos() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_start = end;
        assert_eq!(interval.set_start_offset(new_start), Ok(()));

        assert_eq!(interval.start_offset(), new_start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_start = SignedDuration::from_hours(4);
        assert_eq!(
            interval.set_start_offset(new_start),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_start = SignedDuration::from_hours(2);
        assert_eq!(
            interval.set_start_offset(new_start),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_end_offset {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_end = SignedDuration::from_hours(4);
        interval.unchecked_set_end_offset(new_end);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_end = SignedDuration::from_hours(1);
        interval.unchecked_set_end_offset(new_end);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), new_end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_end = SignedDuration::from_hours(1);
        interval.unchecked_set_end_offset(new_end);

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_offset(), new_end);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod set_end_offset {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_end = SignedDuration::from_hours(4);
        assert_eq!(interval.set_end_offset(new_end), Ok(()));

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), new_end);
    }

    #[test]
    fn ok_same_pos() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_end = start;
        assert_eq!(interval.set_end_offset(new_end), Ok(()));

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), new_end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        let new_end = SignedDuration::from_hours(1);
        assert_eq!(
            interval.set_end_offset(new_end),
            Err(BoundedRelIntervalUpdateError::ChronologicalOrderViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        let new_end = SignedDuration::from_hours(1);
        assert_eq!(
            interval.set_end_offset(new_end),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod set_length_from_start {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        assert_eq!(interval.set_length_from_start(Duration::from_hours(1)), Ok(()));

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), SignedDuration::from_hours(2));
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_incl_excl() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(
            interval.set_length_from_start(Duration::ZERO),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_excl_incl() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Exclusive, end, BoundInclusivity::Inclusive);

        assert_eq!(
            interval.set_length_from_start(Duration::ZERO),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod set_length_from_end {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(3);
        let mut interval = BoundedRelInterval::from_offsets(start, end);

        assert_eq!(interval.set_length_from_end(Duration::from_hours(1)), Ok(()));

        assert_eq!(interval.start_offset(), SignedDuration::from_hours(2));
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_incl_excl() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Inclusive, end, BoundInclusivity::Exclusive);

        assert_eq!(
            interval.set_length_from_end(Duration::ZERO),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }

    #[test]
    fn same_pos_doubly_inclusive_violation_excl_incl() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let mut interval =
            BoundedRelInterval::from_offsets_incl(start, BoundInclusivity::Exclusive, end, BoundInclusivity::Inclusive);

        assert_eq!(
            interval.set_length_from_end(Duration::ZERO),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
        interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));
        interval.unchecked_set_start_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_offset(), interval.end_offset());
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod set_start_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
        assert_eq!(interval.set_start_inclusivity(BoundInclusivity::Exclusive), Ok(()));

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn set_start_inclusivity() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));
        assert_eq!(
            interval.set_start_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
    }
}

mod unchecked_set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
        interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));
        interval.unchecked_set_end_inclusivity(BoundInclusivity::Exclusive);

        assert_eq!(interval.start_offset(), interval.end_offset());
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }
}

mod set_end_inclusivity {
    use super::*;

    #[test]
    fn ok() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
        assert_eq!(interval.set_end_inclusivity(BoundInclusivity::Exclusive), Ok(()));

        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn set_start_inclusivity() {
        let mut interval =
            BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(1));
        assert_eq!(
            interval.set_end_inclusivity(BoundInclusivity::Exclusive),
            Err(BoundedRelIntervalUpdateError::SameOffsetDoublyInclusiveViolation)
        );
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
        Relativity::Relative
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
fn interval_type() {
    let interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
    assert_eq!(interval.interval_type(), IntervalType::Bounded);
}

#[test]
fn interval_type_with_rel() {
    let interval = BoundedRelInterval::from_offsets(SignedDuration::from_hours(1), SignedDuration::from_hours(2));
    assert_eq!(interval.interval_type_with_rel(), IntervalTypeWithRel::RelBounded);
}

mod from_finite_start_end_bounds {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(interval.start(), start);
        assert_eq!(interval.end(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(2));
        let end_pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        let interval = BoundedRelInterval::from((start_pos.to_finite_start_bound(), end_pos.to_finite_end_bound()));

        assert_eq!(interval.start(), end_pos.to_finite_start_bound());
        assert_eq!(interval.end(), start_pos.to_finite_end_bound());
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_end_bound();
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(
            interval.start(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
        );
        assert_eq!(
            interval.end(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
        );
    }
}

mod from_offsetstamp_pair {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(1);
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), start);
    }
}

mod from_offsetstamp_incl_pair {
    use super::*;

    #[test]
    fn ok() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(2);
        let interval =
            BoundedRelInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive)));

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Exclusive);
    }

    #[test]
    fn chronological_order_violation() {
        let start = SignedDuration::from_hours(2);
        let end = SignedDuration::from_hours(1);
        let interval =
            BoundedRelInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive)));

        assert_eq!(interval.start_offset(), end);
        assert_eq!(interval.end_offset(), start);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Exclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = SignedDuration::from_hours(1);
        let end = SignedDuration::from_hours(1);
        let interval =
            BoundedRelInterval::from(((start, BoundInclusivity::Inclusive), (end, BoundInclusivity::Exclusive)));

        assert_eq!(interval.start_offset(), start);
        assert_eq!(interval.end_offset(), end);
        assert_eq!(interval.start_inclusivity(), BoundInclusivity::Inclusive);
        assert_eq!(interval.end_inclusivity(), BoundInclusivity::Inclusive);
    }
}

mod from_finite_bound_pos_pair {
    use super::*;

    #[test]
    fn ok() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(2));
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(interval.start(), start.to_finite_start_bound());
        assert_eq!(interval.end(), end.to_finite_end_bound());
    }

    #[test]
    fn chronological_order_violation() {
        let start = RelFiniteBoundPos::new(SignedDuration::from_hours(2));
        let end = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(interval.start(), end.to_finite_start_bound());
        assert_eq!(interval.end(), start.to_finite_end_bound());
    }

    #[test]
    fn same_pos_doubly_inclusive_violation() {
        let start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
        let end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive);
        let interval = BoundedRelInterval::from((start, end));

        assert_eq!(
            interval.start(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
        );
        assert_eq!(
            interval.end(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
        );
    }
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

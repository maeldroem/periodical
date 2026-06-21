use std::time::Duration;

use jiff::Timestamp;
use jiff::tz::TimeZone;

use super::bound::*;
use crate::intervals::absolute::AbsFiniteBoundPos;
use crate::ops::{Precision, PrecisionMode, PrecisionOutOfRangeError};
use crate::test_utils::datetime_timestamp;

// All implementations and derived functions only use the methods tested below

mod precise_abs_finite_bound_pos {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_finite_bound_pos(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)))
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_finite_bound_pos(
                &AbsFiniteBoundPos::new(Timestamp::MAX),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_finite_bound_pos_with_base_time {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_finite_bound_pos_with_base_time(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)))
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_finite_bound_pos_with_base_time(
                &AbsFiniteBoundPos::new(Timestamp::MAX),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

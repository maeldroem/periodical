use std::time::Duration;

use jiff::Timestamp;
use jiff::tz::TimeZone;

use super::interval::*;
use crate::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos, EmptiableAbsBoundPair};
use crate::ops::{Precision, PrecisionMode, PrecisionOutOfRangeError};
use crate::test_utils::datetime_timestamp;

mod abs_bound_pair {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 0, 0)).to_end_bound()
                ))
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_time {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 34, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 2, 0)).to_end_bound()
                ))
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod emptiable_abs_bound_pair {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 0, 0)).to_end_bound()
                )
                .to_emptiable())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableAbsBoundPair::Empty.precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(EmptiableAbsBoundPair::Empty)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_time {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 34, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 2, 0)).to_end_bound()
                )
                .to_emptiable())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableAbsBoundPair::Empty.precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Ok(EmptiableAbsBoundPair::Empty)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod abs_interval {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 0, 0)).to_end_bound()
                )
                .to_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_time {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 34, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 2, 0)).to_end_bound()
                )
                .to_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod emptiable_abs_interval {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 0, 0)).to_end_bound()
                )
                .to_emptiable_interval())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableAbsBoundPair::Empty
                    .to_emptiable_interval()
                    .precise_different_precisions(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                    ),
                Ok(EmptiableAbsBoundPair::Empty.to_emptiable_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_time {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Ok(AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 34, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 2, 0)).to_end_bound()
                )
                .to_emptiable_interval())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableAbsBoundPair::Empty
                    .to_emptiable_interval()
                    .precise_different_precisions_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 4, 0),
                        Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 2, 0),
                    ),
                Ok(EmptiableAbsBoundPair::Empty.to_emptiable_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 4, 0),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 2, 0),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_abs_bound_pair {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_bound_pair(
                &AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                ),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
            ),
            Ok(AbsBoundPair::new(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound(),
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 0, 0)).to_end_bound()
            ))
        );
    }

    #[test]
    fn precision_out_of_range_error_on_start() {
        assert_eq!(
            precise_abs_bound_pair(
                &AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                ),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }

    #[test]
    fn precision_out_of_range_error_on_end() {
        assert_eq!(
            precise_abs_bound_pair(
                &AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                ),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_bound_pair_with_base_time {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_bound_pair_with_base_time(
                &AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                ),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 4, 0),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 2, 0),
            ),
            Ok(AbsBoundPair::new(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 34, 0)).to_start_bound(),
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 11, 2, 0)).to_end_bound()
            ))
        );
    }

    #[test]
    fn precision_out_of_range_error_on_start() {
        assert_eq!(
            precise_abs_bound_pair_with_base_time(
                &AbsBoundPair::new(
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 50, 0)).to_end_bound()
                ),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 4, 0),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 2, 0),
            ),
            Err(PrecisionOutOfRangeError)
        );
    }

    #[test]
    fn precision_out_of_range_error_on_end() {
        assert_eq!(
            precise_abs_bound_pair_with_base_time(
                &AbsBoundPair::new(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                    AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound()
                ),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 4, 0),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 2, 0),
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

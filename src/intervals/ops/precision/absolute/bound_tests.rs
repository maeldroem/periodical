use std::time::Duration;

use jiff::Timestamp;
use jiff::tz::TimeZone;

use super::bound::*;
use crate::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::ops::{Precision, PrecisionMode, PrecisionOutOfRangeError};
use crate::test_utils::datetime_timestamp;

mod finite_bound_pos {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)))
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX).precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_time {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).precise_with_base_time(
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
                AbsFiniteBoundPos::new(Timestamp::MAX).precise_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod finite_start_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_finite_start_bound()
                    .precise(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_finite_start_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX).to_finite_start_bound().precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_time {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_finite_start_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_finite_start_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX)
                    .to_finite_start_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod finite_end_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_finite_end_bound()
                    .precise(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_finite_end_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX).to_finite_end_bound().precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_time {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_finite_end_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_finite_end_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX)
                    .to_finite_end_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod finite_bound {
    use super::*;

    mod precise {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                        .to_finite_start_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                        .to_finite_end_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }

    mod precise_with_base_time {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                        .to_finite_start_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                        .to_finite_end_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }
}

mod start_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_start_bound()
                    .precise(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                AbsStartBound::InfinitePast.precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsStartBound::InfinitePast)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound().precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_time {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_start_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_start_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                AbsStartBound::InfinitePast.precise_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsStartBound::InfinitePast)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX)
                    .to_start_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod end_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_end_bound()
                    .precise(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_end_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                AbsEndBound::InfiniteFuture.precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsEndBound::InfiniteFuture)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound().precise(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_time {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                    .to_end_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_end_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                AbsEndBound::InfiniteFuture.precise_with_base_time(
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsEndBound::InfiniteFuture)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                AbsFiniteBoundPos::new(Timestamp::MAX)
                    .to_end_bound()
                    .precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod bound {
    use super::*;

    mod precise {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_start_bound()
                        .to_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                        .to_start_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    AbsStartBound::InfinitePast.to_bound().precise(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    ),
                    Ok(AbsStartBound::InfinitePast.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_start_bound()
                        .to_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_end_bound()
                        .to_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                        .to_end_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    AbsEndBound::InfiniteFuture.to_bound().precise(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    ),
                    Ok(AbsEndBound::InfiniteFuture.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_end_bound()
                        .to_bound()
                        .precise(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }

    mod precise_with_base_time {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_start_bound()
                        .to_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                        .to_start_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    AbsStartBound::InfinitePast.to_bound().precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                    Ok(AbsStartBound::InfinitePast.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_start_bound()
                        .to_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_end_bound()
                        .to_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                        .to_end_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    AbsEndBound::InfiniteFuture.to_bound().precise_with_base_time(
                        TimeZone::UTC,
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        datetime_timestamp(2026, 1, 1, 10, 10, 0)
                    ),
                    Ok(AbsEndBound::InfiniteFuture.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_end_bound()
                        .to_bound()
                        .precise_with_base_time(
                            TimeZone::UTC,
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            datetime_timestamp(2026, 1, 1, 10, 10, 0)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }
}

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

mod precise_abs_finite_start_bound {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_finite_start_bound(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_finite_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_finite_start_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_finite_start_bound(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_finite_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_finite_start_bound_with_base_time {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_finite_start_bound_with_base_time(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_finite_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_finite_start_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_finite_start_bound_with_base_time(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_finite_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_finite_end_bound {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_finite_end_bound(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_finite_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_finite_end_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_finite_end_bound(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_finite_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_finite_end_bound_with_base_time {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_abs_finite_end_bound_with_base_time(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_finite_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_finite_end_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_finite_end_bound_with_base_time(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_finite_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_finite_bound {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_abs_finite_bound(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                    .to_finite_start_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_finite_bound(
                    &AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_abs_finite_bound(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                    .to_finite_end_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_finite_bound(
                    &AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_abs_finite_bound_with_base_time {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_abs_finite_bound_with_base_time(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                    .to_finite_start_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_finite_bound_with_base_time(
                    &AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_abs_finite_bound_with_base_time(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                    .to_finite_end_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_finite_bound_with_base_time(
                    &AbsFiniteBoundPos::new(Timestamp::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_abs_start_bound {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_abs_start_bound(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_start_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_abs_start_bound(
                &AbsStartBound::InfinitePast,
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsStartBound::InfinitePast)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_start_bound(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_start_bound_with_base_time {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_abs_start_bound_with_base_time(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_start_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_abs_start_bound_with_base_time(
                &AbsStartBound::InfinitePast,
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsStartBound::InfinitePast)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_start_bound_with_base_time(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_end_bound {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_abs_end_bound(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0)).to_end_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_abs_end_bound(
                &AbsEndBound::InfiniteFuture,
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_end_bound(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_end_bound_with_base_time {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_abs_end_bound_with_base_time(
                &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0)).to_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0)).to_end_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_abs_end_bound_with_base_time(
                &AbsEndBound::InfiniteFuture,
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Ok(AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_abs_end_bound_with_base_time(
                &AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound(),
                TimeZone::UTC,
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                datetime_timestamp(2026, 1, 1, 10, 10, 0)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_abs_bound {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_abs_bound(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_start_bound()
                        .to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                    .to_start_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_abs_bound(
                    &AbsStartBound::InfinitePast.to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsStartBound::InfinitePast.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_bound(
                    &AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound().to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_abs_bound(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_end_bound()
                        .to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 30, 0))
                    .to_end_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_abs_bound(
                    &AbsEndBound::InfiniteFuture.to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(AbsEndBound::InfiniteFuture.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_bound(
                    &AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound().to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_abs_bound_with_base_time {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_abs_bound_with_base_time(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_start_bound()
                        .to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                    .to_start_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_abs_bound_with_base_time(
                    &AbsStartBound::InfinitePast.to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsStartBound::InfinitePast.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_bound_with_base_time(
                    &AbsFiniteBoundPos::new(Timestamp::MAX).to_start_bound().to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_abs_bound_with_base_time(
                    &AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 20, 0))
                        .to_end_bound()
                        .to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsFiniteBoundPos::new(datetime_timestamp(2026, 1, 1, 10, 25, 0))
                    .to_end_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_abs_bound_with_base_time(
                    &AbsEndBound::InfiniteFuture.to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Ok(AbsEndBound::InfiniteFuture.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_abs_bound_with_base_time(
                    &AbsFiniteBoundPos::new(Timestamp::MAX).to_end_bound().to_bound(),
                    TimeZone::UTC,
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    datetime_timestamp(2026, 1, 1, 10, 10, 0)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

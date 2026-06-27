use std::time::Duration;

use jiff::SignedDuration;

use super::interval::*;
use crate::intervals::relative::{EmptiableRelBoundPair, RelBoundPair, RelFiniteBoundPos};
use crate::ops::{Precision, PrecisionMode, PrecisionOutOfRangeError};

mod rel_bound_pair {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(60)).to_end_bound()
                ))
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_offset {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(34)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(62)).to_end_bound()
                ))
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod emptiable_rel_bound_pair {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(60)).to_end_bound()
                )
                .to_emptiable())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableRelBoundPair::Empty.precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(EmptiableRelBoundPair::Empty)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_offset {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(34)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(62)).to_end_bound()
                )
                .to_emptiable())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableRelBoundPair::Empty.precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Ok(EmptiableRelBoundPair::Empty)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .to_emptiable()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod rel_interval {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(60)).to_end_bound()
                )
                .to_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_offset {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(34)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(62)).to_end_bound()
                )
                .to_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .to_interval()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod emptiable_rel_interval {
    use super::*;

    mod precise_different_precisions {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(60)).to_end_bound()
                )
                .to_emptiable_interval())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableRelBoundPair::Empty
                    .to_emptiable_interval()
                    .precise_different_precisions(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                    ),
                Ok(EmptiableRelBoundPair::Empty.to_emptiable_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_different_precisions_with_base_offset {
        use super::*;

        #[test]
        fn ok_bound() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Ok(RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(34)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(62)).to_end_bound()
                )
                .to_emptiable_interval())
            );
        }

        #[test]
        fn ok_empty() {
            assert_eq!(
                EmptiableRelBoundPair::Empty
                    .to_emptiable_interval()
                    .precise_different_precisions_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(4),
                        Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(2),
                    ),
                Ok(EmptiableRelBoundPair::Empty.to_emptiable_interval())
            );
        }

        #[test]
        fn precision_out_of_range_error_on_start() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }

        #[test]
        fn precision_out_of_range_error_on_end() {
            assert_eq!(
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                )
                .to_emptiable_interval()
                .precise_different_precisions_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(4),
                    Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(2),
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_rel_bound_pair {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_bound_pair(
                &RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                ),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
            ),
            Ok(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_mins(60)).to_end_bound()
            ))
        );
    }

    #[test]
    fn precision_out_of_range_error_on_start() {
        assert_eq!(
            precise_rel_bound_pair(
                &RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                ),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }

    #[test]
    fn precision_out_of_range_error_on_end() {
        assert_eq!(
            precise_rel_bound_pair(
                &RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                ),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_bound_pair_with_base_offset {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_bound_pair_with_base_offset(
                &RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                ),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(4),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                SignedDuration::from_mins(2),
            ),
            Ok(RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_mins(34)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_mins(62)).to_end_bound()
            ))
        );
    }

    #[test]
    fn precision_out_of_range_error_on_start() {
        assert_eq!(
            precise_rel_bound_pair_with_base_offset(
                &RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_mins(50)).to_end_bound()
                ),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(4),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                SignedDuration::from_mins(2),
            ),
            Err(PrecisionOutOfRangeError)
        );
    }

    #[test]
    fn precision_out_of_range_error_on_end() {
        assert_eq!(
            precise_rel_bound_pair_with_base_offset(
                &RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound()
                ),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(4),
                Precision::unchecked_new(Duration::from_mins(20), PrecisionMode::ToFuture),
                SignedDuration::from_mins(2),
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

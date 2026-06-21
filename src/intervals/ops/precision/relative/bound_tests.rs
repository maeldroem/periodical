use std::time::Duration;

use jiff::SignedDuration;

use super::bound::*;
use crate::intervals::relative::RelFiniteBoundPos;
use crate::ops::{Precision, PrecisionMode, PrecisionOutOfRangeError};

// All implementations and derived functions only use the methods tested below

mod precise_rel_finite_bound_pos {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_bound_pos(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)))
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_bound_pos(
                &RelFiniteBoundPos::new(SignedDuration::MAX),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_bound_pos_with_base_offset {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_bound_pos_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)))
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_bound_pos_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::MAX),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

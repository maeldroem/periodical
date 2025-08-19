use chrono::{Duration, Utc};

use crate::intervals::meta::BoundInclusivity;
use crate::prelude::{ClosedAbsoluteInterval, ClosedRelativeInterval};
use crate::test_utils::date;

use super::relativity_conversion::*;

#[test]
fn no_op_absolute_to_absolute() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
        .to_absolute(date(&Utc, 2000, 1, 1)),
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn no_op_relative_to_relative() {
    assert_eq!(
        ClosedRelativeInterval::new_with_inclusivity(
            Duration::zero(),
            BoundInclusivity::Inclusive,
            Duration::days(1),
            BoundInclusivity::Exclusive,
        )
        .to_relative(date(&Utc, 2000, 1, 1)),
        ClosedRelativeInterval::new_with_inclusivity(
            Duration::zero(),
            BoundInclusivity::Inclusive,
            Duration::days(1),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn from_absolute_to_relative() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
        .to_relative(date(&Utc, 2025, 1, 1)),
        ClosedRelativeInterval::new_with_inclusivity(
            Duration::zero(),
            BoundInclusivity::Inclusive,
            Duration::days(1),
            BoundInclusivity::Exclusive,
        ),
    );
}

#[test]
fn from_relative_to_absolute() {
    assert_eq!(
        ClosedRelativeInterval::new_with_inclusivity(
            Duration::zero(),
            BoundInclusivity::Inclusive,
            Duration::days(1),
            BoundInclusivity::Exclusive,
        )
        .to_absolute(date(&Utc, 2025, 1, 1)),
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        ),
    );
}

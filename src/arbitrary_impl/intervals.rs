//! Manual implementations of the [`Arbitrary`] trait on interval types

use arbitrary::{Arbitrary, Unstructured};
use chrono::{DateTime, Duration, Utc};

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound, ClosedAbsoluteInterval};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{ClosedRelativeInterval, RelativeBounds, RelativeEndBound, RelativeStartBound};

impl<'a> Arbitrary<'a> for AbsoluteBounds {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = AbsoluteStartBound::arbitrary(u)?;
        let end = AbsoluteEndBound::arbitrary(u)?;

        // We use AbsoluteBounds::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(AbsoluteBounds::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for ClosedAbsoluteInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start_time = DateTime::<Utc>::arbitrary(u)?;
        let end_time = start_time.checked_add_signed(Duration::arbitrary(u)?).unwrap_or(start_time);

        if start_time == end_time {
            Ok(ClosedAbsoluteInterval::new_with_inclusivity(
                start_time,
                BoundInclusivity::Inclusive,
                end_time,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(ClosedAbsoluteInterval::new_with_inclusivity(
                start_time,
                BoundInclusivity::arbitrary(u)?,
                end_time,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}

impl<'a> Arbitrary<'a> for RelativeBounds {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = RelativeStartBound::arbitrary(u)?;
        let end = RelativeEndBound::arbitrary(u)?;

        // We use RelativeBounds::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(RelativeBounds::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for ClosedRelativeInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start_offset = Duration::arbitrary(u)?;
        let length = Duration::arbitrary(u)?;

        if length.is_zero() {
            Ok(ClosedRelativeInterval::new_with_inclusivity(
                start_offset,
                BoundInclusivity::Inclusive,
                length,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(ClosedRelativeInterval::new_with_inclusivity(
                start_offset,
                BoundInclusivity::arbitrary(u)?,
                length,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}

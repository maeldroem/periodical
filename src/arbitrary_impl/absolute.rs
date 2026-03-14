//! [`Arbitrary`] implementations for items within the [`absolute`](crate::intervals::absolute) module

use arbitrary::{Arbitrary, Error, Unstructured};
use jiff::Timestamp;

use crate::intervals::absolute::AbsoluteFiniteBound;
use crate::intervals::meta::BoundInclusivity;

impl<'a> Arbitrary<'a> for AbsoluteFiniteBound {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let timestamp_range = Timestamp::MIN.as_nanosecond()..=Timestamp::MAX.as_nanosecond();
        let timestamp = Timestamp::from_nanosecond(u.int_in_range(timestamp_range)?)
            .or(Err(Error::IncorrectFormat))?;

        Ok(Self::new_with_inclusivity(timestamp, BoundInclusivity::arbitrary(u)?))
    }
}

/*
impl<'a> Arbitrary<'a> for AbsoluteBounds {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = AbsoluteStartBound::arbitrary(u)?;
        let end = AbsoluteEndBound::arbitrary(u)?;

        // We use AbsoluteBounds::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(AbsoluteBounds::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for BoundedAbsoluteInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start_time = DateTime::<Utc>::arbitrary(u)?;
        let end_time = start_time
            .checked_add_signed(Duration::arbitrary(u)?)
            .unwrap_or(start_time);

        if start_time == end_time {
            Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                start_time,
                BoundInclusivity::Inclusive,
                end_time,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(BoundedAbsoluteInterval::new_with_inclusivity(
                start_time,
                BoundInclusivity::arbitrary(u)?,
                end_time,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}
*/

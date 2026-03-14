//! [`Arbitrary`] implementations for items within the [`relative`](crate::intervals::relative) module

use arbitrary::{Arbitrary, Error, Unstructured};
use jiff::SignedDuration;

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::RelativeFiniteBound;

impl<'a> Arbitrary<'a> for RelativeFiniteBound {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();
        let signed_duration = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range)?)
            .ok_or(Error::IncorrectFormat)?;

        Ok(Self::new_with_inclusivity(signed_duration, BoundInclusivity::arbitrary(u)))
    }
}

/*
impl<'a> Arbitrary<'a> for RelativeBounds {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = RelativeStartBound::arbitrary(u)?;
        let end = RelativeEndBound::arbitrary(u)?;

        // We use RelativeBounds::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(RelativeBounds::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for BoundedRelativeInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start_offset = Duration::arbitrary(u)?;
        let length = Duration::arbitrary(u)?;

        if length.is_zero() {
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                start_offset,
                BoundInclusivity::Inclusive,
                length,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(BoundedRelativeInterval::new_with_inclusivity(
                start_offset,
                BoundInclusivity::arbitrary(u)?,
                length,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}
*/

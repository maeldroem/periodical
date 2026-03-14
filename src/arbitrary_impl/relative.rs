//! [`Arbitrary`] implementations for items within the [`relative`](crate::intervals::relative) module

use arbitrary::{Arbitrary, Unstructured};

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
